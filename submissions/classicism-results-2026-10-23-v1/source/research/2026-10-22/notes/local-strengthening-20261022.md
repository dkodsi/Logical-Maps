# Local strengthenings and Strong Possibility: research audit

22 October 2026. Original arguments by OpenAI Codex research subagent; not human checked or formalized. Direct source of new arguments: misc, the sections below. No database edits. Background: Bacon–Dorr, Classicism, draft 16 May 2023, Appendix E pp. 80–83; the author-hosted July 2022 draft, https://andrew-bacon.github.io/papers/Classicism.pdf, Appendix E pp. 78–81, explicitly permits arbitrary root individual sets on p. 81. Keep those pagination systems distinct.

## 1. Full second-order local transfer

Let T be a full second-order relational theory on a nonempty set E, using individual variables and n-ary relation variables on individuals. Equality between relations must be read as actual coextension; no intensional relation identity occurs. Suppose a full ordinary structure on E satisfies T.

Take a C-complete family of action-model components and form a coalesced root with individual domain E and arbitrary counterpart maps E to each chosen component individual domain. The pure-language version has no individual constants whose interpretations must be preserved. The arbitrary-root construction is explicitly allowed in the source. Retain fullest root relational domains.

Every subset of E^n is an actual extension of a root n-ary relation, by choosing that extension and arbitrary component coordinates. Therefore evaluation of every formula of the stated second-order fragment at the root agrees with full ordinary second-order evaluation on E. This is a structural induction: individual equality is genuine equality, applications use the actual extensions, classical connectives and individual quantifiers have their ordinary clauses, and relation quantifiers range surjectively over all extensions. Multiple intensions with the same extension do not matter in this fragment.

Choosing the designated relations' root extensions gives T at the root. Complete components give pure Maximalism. Existentially close any designated relations/constants of a finite structure assertion to obtain a closed pure sentence. Thus, for example, the existence of a full second-order Peano structure on all individuals and the existence of a Dedekind-complete ordered field on all individuals are individually consistent with pure Max. They are strict strengthenings: the recorded singleton-root Max model falsifies each. These are local mathematical commitments; no necessity-of-arithmetic claim follows. An infinite T can be realized under one existential interpretation of its signature, but one must not replace that by separate existential closures of its axioms and claim the latter assert a shared structure.

A narrower cardinal example: the root proposition domain is 2 times the product of component propositional domains, independently of E. Choose E equipotent to that set. A root relation of type ett with a graph as its actual extension witnesses an actual relational bijection between individuals and propositions. This is compatible with pure Max and false at the singleton-root Max model. It is NOT a surjective operation e→t: such an operation would have outputs top and bottom, forcing two necessarily distinct individuals and contradicting Max's possible monism.

## 2. Unary Possibility+ follows from pure Max

Fix any pure C-consistent formula P(x) with at most one free individual variable. Take a C-model with witness b, and add a singleton root whose sole individual maps to b. At that root Q := E_1 and forall x diamond P(x) is true. Thus the closed pure Q is C-consistent.

Pure Max gives diamond Q. For each actual individual a, Q implies diamond P(a) at a Q-world, by universal instantiation and total counterpart transport. Hence diamond diamond P(a), and by 4, diamond P(a). Generalize a.

Equivalently, pure Max implies Maximalism for a signature with one individual constant and no relational constants, for every interpretation of that constant. Apply the unary theorem to A(x) != B(x) whenever the corresponding one-constant identity is not C-provable, then use NI to infer actual inequality from possible inequality.

Pure Strong Possibility implies E_1 by the recorded argument. Consequently it implies every pure Possibility+ instance: the empty tuple is pure Max, the one-variable cases are the theorem above, and the distinctness antecedents for two or more variables are false under E_1.

The proved-only Engine did not already derive SP→Possibility+. It does already exclude SP together with all-type BF or Functionality, through possible Infinity_e and the recorded SP/Infinity_e incompatibility. The direct type-e sharpening is: under E_1, BF_e gives necessary E_1; Functionality for e→t identifies the sole individual's haecceity with top and likewise gives necessary E_1. Pure Max rules this out.

## 3. Universal identity fragment

If U is a pure sentence forall xbar theta(xbar), with theta a finite Boolean combination of typed term identities, then C proves diamond_ne U → U. For an actual countertuple, put its true literals in disjunctive normal form. Positive identities remain true ordinarily by NI. Let q be the finite conjunction of its true disequalities, or top if none. Then q is true, and necessarily diamond q makes all those disequalities true by contraposition of NI. Thus necessarily diamond q implies not-U; q witnesses box_ne not-U. This proves the contrapositive directly, without presuming a separate Barcan principle for the hat modality.

Therefore pure SP entails every Max-compatible U in this fragment. Functionality is not such a universal sentence after prenexing: its inner universal antecedent yields an existential quantifier. Atomhood of a fixed proposition is in the fragment because Boolean order is a Boolean identity.

No actual contradiction of pure SP was obtained from this criterion.

## 4. Sufficient named-neighborhood criterion for SP

Suppose a pure-Max model has the following external property: for each true actual proposition q there are an individual a and a pure formula Q(x), with no other free variables, such that Q(a) is true and Q(a) <= q. Then the model satisfies pure SP.

Fix Max-consistent pure P. Since Q(a) is true in a C-model, Q(x) is C-consistent. Section 2 makes forall x diamond Q(x) a consequence of pure Max. Hence P and diamond Q(x) is C-consistent. Applying section 2 at the given root gives diamond(P and diamond Q(a)). The actual identity expressing Q(a)<=q is necessary by NI, so necessarily diamond Q(a) implies diamond q. Thus diamond(P and diamond q). Since q was any true proposition, the dual definition of diamond_ne yields diamond_ne P.

The special case in which every actual proposition is a pure term evaluated at one distinguished individual also suffices. Existence of a model with either property remains unproved. Pure-term generation WITHOUT an individual parameter is impossible: the pure unary formula A(x):=forall y(x=y or box(x!=y)) is nonuniform in a three-individual idempotent-collapse action model, so C proves A(x)=Q for no closed pure Q. Section 2 therefore makes A(a) distinct from every closed pure Q in any pure-Max model.

## 5. Audit of the parent's profile-root construction

Read /tmp/classicism-research/profile-root-construction-20261022.md sections 1–5. The construction passes this independent agent audit:

- A parameterized abstraction's profile is the pure term obtained by substituting the finitely many parameter profiles before abstraction. At each component, its quantifiers range over the unchanged component domains. At the root, its actual extension is admitted freely. No transport-surjectivity assumption is used.
- Application follows term substitution and actual fibers; eta follows component eta and equality of actual fibers. The logical universal quantifier has its usual pure profile and the actual universal-truth test as root extension.
- Finite Fregean n-individual structures are full at every finite type by finite lambda case distinctions and Extensionality. Pointed pure terms have invariant truth there. Thus the claimed finite-world propositions A_n are indeed atoms.
- The standard numeral set is an admitted root subset of the cardinality type. Its members are distinct via finite components. The countable profile set has an explicit syntactic enumeration, and the arbitrary root graph relation gives the stated Ctbl injection.

## 6. Why simply removing the free root bit does not construct SP

In the profile-root construction, retaining both (0,b) and (1,b) for the same propositional profile b produces the true root-only proposition by exclusive disjunction. Hence avoiding Actuality requires actual truth to be a function v of the retained propositional profile.

If all root entities still have one-individual-term profiles, application then forces every relation's actual extension to be S_T(abar)=v([T(Ubar)]), where the U_i are the argument profiles. Identity forbids distinct root entities sharing a profile: their identity proposition would have profile top, which has true actual value. Consequently arbitrary actual higher extensions cannot be retained after dropping the propositional bit.

The natural fully term-profile variant reduces to the term algebra over C(z), with a truth ultrafilter v satisfying Max(C(z))+E_1 and, crucially, every Henkin condition

v([forall x phi])=1 iff v([phi(U)])=1 for every admitted term-profile U.

Existence of such a Henkin truth assignment is the unproved mathematical obligation. A mere ultrafilter on the Boolean algebra of profiles does not establish the reverse quantifier implication. This is a reduction of the construction problem, not a consistency proof or an inconsistency result.

## 7. Finite relational signatures: exact singleton atom decomposition

Let Sigma be finite and have relational constants only. Write A_1=Fregean and E_1. In the unique full singleton extensional hierarchy, every relational entity has a closed pure representative: induct on type, using constant output when the argument type is e, and finite truth-table case distinctions when its argument type is relational. Hence there are finitely many complete interpretations d of Sigma, each specified under A_1 by a conjunction D_d of identities c=T_(c,d) to these representatives.

Put B_d=A_1 and D_d. C(Sigma) proves that A_1 is the disjoint join of the B_d, and every B_d is C(Sigma)-consistent. Max(C(Sigma)) makes each B_d nonzero.

Generalize the parent's profile-root model by letting profiles be Sigma-terms T(z), and taking components complete for C(Sigma), with the constants interpreted by their own profiles. Under any B_d there is a unique pointed finite extensional structure: E_1 leaves exactly one possible marker z. Thus each T(z) has constant truth on B_d. The profile argument makes every B_d an atom simultaneously. A_1 is actually false at the root since pure Max refutes Fregean. This certifies Max(C(Sigma))+all Atom(B_d).

Atom(B_d) is a universal identity formula, so Strong Possibility for Sigma entails every Atom(B_d). Accordingly A_1 is a finite disjoint join of exactly k atoms, where k is the product, over the constants c, of the size of c's type in the singleton extensional hierarchy. Those sizes obey N_e=1, N_t=2, N_(sigma tau)=N_tau^(N_sigma). Any nonempty relational Sigma gives k at least two. There is no hidden one-individual marker obstruction at E_1.

## 8. The pointed-completeness criterion (finite relational-only signature)

The unary Possibility+ theorem of section 2 generalizes to Sigma-formulas if Sigma has no individual constants: relational constants glue across the singleton-root construction. This fails in general when individual constants are present; P(x):=x!=c is the immediate obstruction to unrestricted unary lifting.

For a closed Sigma-sentence B with C(Sigma)+B consistent, define pointed completeness as follows: for every Sigma-formula phi(x) with at most one free individual variable, either C(Sigma) proves B→forall x phi(x), or it proves B→forall x not-phi(x).

Claim: for finite relational-only Sigma, Max(C(Sigma))+Atom(B) is consistent if and only if B is pointed complete.

Necessity. If both B and phi(x), and B and not-phi(x), are C(Sigma)-consistent, unary Possibility+ supplies both possibilities for every actual a. Thus the root proposition phi(a) splits B into two nonzero parts, contradicting Atom(B).

Sufficiency. In the Sigma-profile root, pointed completeness makes every profile T(z) constant on B; hence the profile of p and B is bottom or B. Moreover B is actually false there. For if B were true in a Max model, completeness of the finitely axiomatized theory C(Sigma)+B would force that consistent recursively enumerable theory to contain every Max(C(Sigma)) axiom. That contradicts the undecidability argument in the parent's profile-root note section 8 (the proof works for any finite signature). Consequently the actual coordinate of p and B is zero, and B is an atom. Nonzeroness follows from C(Sigma)-consistency and Max.

This distinguishes complete CLOSED theories from pointed completeness. For example, a two-individual Fregean structure with a unary constant true of exactly one individual has a complete unpointed finite theory B, but its marker roles differ. Both B and c(x), and B and not-c(x), are consistent. Therefore B cannot be an atom in any Max(Sigma) model. A proposed profile construction choosing just one marker orbit cannot remain complete and closed under composition: singleton-root component theories require paths to both marker roles.

## 9. An independent family of finite-world atom axioms over pure Max

Let A_n=Fregean and E_n, for each positive integer n. For EVERY set S of positive integers there is a pure-Max model satisfying Atom(A_n) exactly for n in S. In particular these axioms form an independent countable family over pure Max, and all can hold together.

Construction. For each n outside S introduce an auxiliary propositional symbol d_n. Begin with a set of pure C-components complete for C. Include all their expansions in which each d_n is interpreted, throughout that component, as either the pure proposition A_n or bottom. Include the full finite extensional n-individual components in both choices for d_n, whenever n is outside S. The auxiliary symbols describe the construction; the final assertion concerns the PURE reduct.

Use the parent's singleton profile-root construction, now allowing profiles T(z,d_n,...) containing only finitely many auxiliary symbols. Root domains still pair arbitrary actual extensions with these profiles. Closure under terms is exactly the substitution argument already audited: profiles of finitely many parameters can be substituted into the term, and auxiliary interpretations transport as ordinary nonlogical constants. Each expanded component is a C-model, and the family remains complete for pure C. Thus the root satisfies pure Max. It refutes Fregean, so every A_n is actually false.

If m belongs to S, then at every component point satisfying A_m, each auxiliary d_n equals bottom: n is outside S and hence n differs from m, and A_n is false in that Fregean m-individual structure. All profiles consequently reduce there to pure one-individual-parameter terms in the unique full finite m-individual structure. Individual permutations make their propositional truth uniform. For every root p, p and A_m is therefore either bottom or A_m, at the profile level and at the zero actual coordinate. So A_m is an atom.

If n is outside S, the root entity with profile d_n splits A_n. One full n-individual component interprets d_n=A_n=top, and another interprets d_n=bottom. Thus both A_n and d_n, and A_n and not-d_n, are nonzero. Hence A_n is not an atom.

Only countably many extra symbols are used, so the profile set remains countable. The internal-countability proof in the parent's profile-root note section 5 applies unchanged. Accordingly every independence pattern above is simultaneously consistent with the internal statement Ctbl_(e,t)(top_t).

This is an original restricted-profile construction, not a result attributed to the source paper. It does not supply Strong Possibility; the arbitrary actual coordinate still gives Actuality, and pure SP only selects the all-atom pattern as a necessary condition.

## 10. Strong Possibility is incompatible across finite signature extensions

Let Sigma be finite and relational-only, and let Sigma' add at least one fresh relational constant d. Then SP_Sigma + Max(C(Sigma')) is inconsistent; in particular SP_Sigma and SP_Sigma' cannot both hold.

Choose any complete singleton diagram B of section 7. SP_Sigma entails Atom(B). Let R(d) universally apply d to all of its argument places (R(d)=d at type t). Holding the old finite singleton structure fixed, interpret d as top or bottom. Thus both B and R(d), and B and not-R(d), are C(Sigma')-consistent. Max(C(Sigma')) makes both propositions nonzero. They split B, contradicting its atomhood. The conclusion concerns the generic/maximal expansion, not an arbitrary expansion interpreting d as a previously available entity.

There is a broader finite-signature version. If Sigma has k≥1 individual constants, a coalesced root with those k constants as its entire individual domain is Max(C(Sigma))-consistent. Max makes those constants actually distinct. E_k is co-persistent under diamond_ne, so SP_Sigma forces exactly k individuals, and every individual is named by an individual constant. A restricted profile-root can use CLOSED Sigma-term profiles, with its k root individuals represented by those constants. Every complete finite full-extensional Sigma-structure diagram B then becomes an atom: no extra unnamed root-individual profile is needed. Fregean falsity again makes B's actual coordinate zero. The same fresh-relational-constant argument applies. For zero individual constants, use the singleton pointed construction of section 7.

This does not prove any one fixed-signature SP theory inconsistent. It shows why signature/reference-theory changes cannot be silently treated as harmless conservativity steps. Adding just one individual constant to a relational-only signature is not covered by the fresh-relational-constant argument.

## 11. Finite relational signatures: decomposition by pointed structures

This strengthens section 7 beyond the singleton cell. Fix a positive standard n and a finite relational-only signature Sigma. There are finitely many isomorphism classes of full extensional n-individual Sigma-structures with one distinguished individual. Let their number be K_Sigma(n). Equivalently, fix an n-element set and one marker; K_Sigma(n) is the number of orbits of the marker's permutation stabilizer on the finite set of all interpretations of the signature constants in the full finite hierarchy.

Each pointed isomorphism class i has a finite formula D_i(x): enumerate the n individuals by variables, require their distinctness and exhaustion, give complete finite tables for the finitely many signature constants using those variables, and specify the marker. All types occurring in these tables are finite, and finite lambda case distinctions supply their representatives. Conjoin F and E_n. The D_i(x) are mutually exclusive and their disjunction is A_n, provably in C(Sigma).

In the singleton Sigma-profile root, D_i(a) is nonbottom, and any profile T(z) has a uniform truth value on the arrows satisfying D_i(z): those targets are isomorphic pointed structures. Since F is false at the root, the actual coordinate of D_i(a) is zero. The same argument as section 5 therefore makes every D_i(a) an atom, simultaneously. Consequently Max(C(Sigma)) together with forall x Atom(D_i(x)) is consistent. This latter sentence is a universal Boolean combination of typed identities, so SP_Sigma forces it.

It follows that SP_Sigma makes A_n the disjoint join of exactly K_Sigma(n) atoms, for every positive standard n. A finite universal equivalent upper-bound sentence says that A_n contains no K_Sigma(n)+1 pairwise disjoint nonzero parts; Max alone supplies the lower bound by unary Possibility+Sigma applied to the pointed diagrams. These constraints coexist in the Sigma-profile-root model, although full SP consistency remains open.

Examples: for the empty signature K(n)=1; for one propositional constant K(n)=2; for one unary individual predicate constant K(n)=2n, indexed by the predicate's extension size and whether the marker belongs. More locally, a fixed unpointed finite structure M with r individual automorphism orbits has its diagram B_M split into exactly r atoms under SP_Sigma, represented by B_M and the orbit formulas O_i(a). This also explains section 8's obstruction: B_M itself can be atomic exactly when the individual action is transitive.

## 12. Audit of two additional constructions

The parent's profile-root note section 13 upgrades section 9 to atomic versus atomless choices: use countably many auxiliary generators d_(n,j) for each unprotected n. Every nonzero part p of A_n uses finitely many generators in its profile. Duplicate a component realizing p, keep those finitely many interpretations fixed, and toggle a fresh d_(n,j) between A_n and bottom. The two meets with the fresh generator and its complement are nonzero. Protected cells remain atomic because all generators indexed by different cardinalities are bottom as entities at their Fregean targets. This passes the modal-identity audit; actual falsity alone would not have sufficed outside those cells.

The parent's additional finite rigid cells B_(n,k):=Box(E_n^e and E_(2^k)^t and ND_e and ND_t), n,k positive, also pass an independent audit. At every reachable object the e and t transport maps are bijective by injectivity and the boxed exact cardinalities. Inductively, bijectivity of argument transports makes a relation determined by its actual entity-valued function, because every future argument lifts. Finite crisp equality cases realize every function. Higher-type transports are therefore induced bijections. This proves FUNCTIONALITY, not Extensionality: equal actual truth extensions need not identify relations when k>1.

The resulting structure is the full function hierarchy over the finite Boolean algebra with k atoms and an n-element individual set. Quantifiers are finite meets. Boolean-atom permutations and individual permutations act transitively on the pair consisting of the truth ultrafilter and individual marker. Thus the cell is pointed-complete; a rigid constant-domain k-world S5 model realizes it. The parent's pointed-completeness criterion makes B_(n,k) consistently atomic with Max and therefore atomic under SP. Incompatible boxed cardinalities make distinct cells bottom entities at each other's worlds, so the same independent selector construction applies to them.

The separate note infinitary-standard-numerals-20261022.md also passes this audit relative to its explicitly cited local arithmetic lemmas. Its numeral-range comprehension gives externally standard numerical domains at every world; I implies I-star without CBC, and the recorded Peano recursion laws then make arithmetic standard at I-worlds. This contradicts the two old-Max arithmetic branches supplied by incompleteness. Gödel--Rosser is the precise incompleteness version using consistency alone. The result concerns the specified infinitary enrichment and the OLD finitary Max reference theory; it does not refute finitary SP.

## 13. Removing Actuality does not repair the naive omitting-types argument

Let T_0 be Max+E_1+not-Actuality, and let a name its sole individual. The reflection lane's independently audited hybrid construction has a world W satisfying T_0 and propositional Atomlessness; see reflection-retract-fragments-20261022.md section 4. Max makes A_1 nonzero there, so the formula theta(p):=bottom<p<A_1 is consistent with T_0.

For each pure proposition term Q(x) with only one possible free individual variable, pointed completeness of A_1 gives either C proves forall x Box(A_1->Q(x)), or C proves forall x Box(A_1->not-Q(x)). Thus Q(a) cannot be a proper nonzero part of A_1. Consequently theta(p) implies p!=Q(a), for every such term Q. The partial type consisting of all those inequalities is therefore locally isolated even over T_0.

Accordingly the standard nonprincipal-type hypothesis for a direct omitting-types construction still fails after adding not-Actuality and monism. At minimum the theory must also prohibit these splitters, by adding Atom(A_1), and similarly for every other pointed-complete closed cell. This does not prove that term-generation models are impossible over T_0: they may omit the isolating formula as well. It does not obstruct the weaker named-TRUE-neighborhood criterion of section 4, since every p satisfying theta is false at a Max world.
