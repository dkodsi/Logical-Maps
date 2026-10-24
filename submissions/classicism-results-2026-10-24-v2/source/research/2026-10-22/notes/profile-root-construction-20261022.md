# Pure-term-profile root: original construction and consequences

Date: 22 October 2026. Author: OpenAI Codex research subagent. Ordinary mathematical argument, not independently human checked and not Lean formalized. No database files edited. Direct source of the new construction and deductions: misc, this note §§1–5. Background construction: Bacon–Dorr, *Classicism*, draft 16 May 2023, Appendix E pp. 80–83; the available author-hosted July 2022 draft has Appendix E pp. 78–81 and explicitly allows arbitrary root individual sets on p. 81. These are different pagination systems. This is a restricted-domain variation, not a claim that the paper proves the new results.

## 1. Construction

Fix a set of pure-language action models complete for C, with disjoint component categories. Include every object of each component when taking the following arrows. Add a new root o with one individual *. There are no nonidentity arrows from o to itself. For each component object V and each a in its individual domain, add an arrow h_(V,a):o→V. Composition is k h_(V,a)=h_(V',k·a) for k:V→V'. The components themselves are unchanged. The root individual transports to a along h_(V,a).

Fix a single free individual variable z. A profile at type σ is a pure term T(z) of type σ, with no free variables other than z, identified with the family of its values T^V(a) over all component objects V and individuals a. Different syntax with identical such families is identified. Profiles form a countable set B_σ; a relational type always has profiles, for example bottom. For type e the root's sole individual has profile z.

Inductively, at a relational type σ=τ_1…τ_k t, let

D_σ(o) = P(D_τ1(o)×…×D_τk(o)) × B_σ.

For k=0 this is 2×B_t. The first coordinate is an arbitrary actual extension; the second is its profile. Transport of (S,[T]) along h_(V,a) is T^V(a). The pair is determined by its intension: the identity arrow sees S, and the outgoing arrows see the profile family.

Application takes the corresponding fiber of S at the actual argument. Its component profile is obtained by term application: substitute the argument's profile U(z), or z for the sole individual, into T(z). Thus it is again a profile. The profile of each logical operation is its usual pure term. Identity at the root is literal identity of pairs (and of the sole individual). Quantifiers at the root range over the root domains; at a component target they range over that component's domains, as action-model semantics requires. Do NOT replace this by a single constant global-domain semantics, which would incorrectly demand surjectivity of root transports.

## 2. Closure and validity of C

A term with finitely many root parameters has a profile: choose a pure one-variable profile for each parameter and substitute these profiles into the term, using capture-avoiding substitution. At each component arrow, its value is exactly that substituted term's component value. This follows by induction on the term, including quantifiers because at a component the quantifier ranges over the original component domain. Transport along a component arrow commutes with term interpretation, so the profile lands in the component domain and satisfies the required compatibility.

At the root, an abstraction has whichever actual extension its defining formula has over the root domains. Every such extension is admitted. Its profile is the substituted pure abstraction just described. Therefore all terms are admitted. Beta is immediate; eta follows from equality of actual extensions and eta for the profile terms. The classical truth-functional and quantifier clauses and literal identity validate H at the root. The components already validate H. If two formulas are H-equivalent, their abstractions have the same actual extension at the root, and identical profile families because each component validates C. Hence their pair denotations are identical. This verifies Logical Equivalence with its theoremhood condition and therefore C.

This is a construction of an action model with restricted root domains. It does not assume that restricting arbitrary models to term denotations preserves quantification.

## 3. Pure Maximalism

Every C-consistent closed pure sentence P is true at an object V of a selected component. Choose any a in V's nonempty individual domain. The arrow h_(V,a) witnesses P's possibility at o. Thus pure Maximalism holds at o.

The arbitrary root coordinate gives a singleton root proposition (true at the identity, bottom profile), so Actuality and the usual isolated-root distinctness-preserving collapse hold. Consequently this particular model is NOT a model of Strong Possibility. Its role for SP is to certify the Max-consistency of additional sentences.

## 4. Every finite extensional pure theory is a propositional atom

For n≥1 put A_n := F ∧ E_n, where F is the Fregean Axiom and E_n says that exactly n individuals exist. Each is a closed pure sentence. We claim Atom_t(A_n) holds at o, simultaneously for every n.

At a world satisfying F and E_n, the local typed structure is uniquely the full extensional Henkin structure on n individuals. F gives two propositions and Extensionality. Inductively every higher type is finite; lambda abstraction with parameters realizes each subset of the finite argument domain, so there are no omitted extensions. Every permutation of the n individuals extends to an automorphism of this full structure. Therefore for any pure proposition term T(z), its truth value is the same at every such pointed structure (V,a): it is independent of the chosen V and a.

Consequently for each root proposition p=(b,[T(z)]), the profile of p∧A_n is either uniformly bottom or the profile of A_n. Also A_n is actually false at o: there are infinitely many root propositions, so F fails. Hence the actual coordinate of p∧A_n is 0 in either case. Thus p∧A_n is either bottom or A_n. A_n is nonbottom because a full n-individual extensional component realizes it. This is exactly atomicity of A_n in the root Boolean algebra.

In particular pure Maximalism plus all the sentences Atom_t(A_n) is consistent. These atom assertions are original consequences of the present construction. Pure completeness alone is not the exact criterion: §12 below proves the sharper characterization using pointed completeness. The same profile root realizes all its positive atom laws simultaneously.

## 5. Internally countably many propositions

The root proposition domain 2×B_t is externally countably infinite. Infinitude follows, for example, from the distinct profiles E_n, separated in full finite extensional components.

Let ν_e=(et)t and N_e be FiniteCardinality_e as defined in the topic. The root N_e extension is exactly the set of standard numeral denotations 0_e,Suc_e(0_e),… . Every standard numeral is in N_e by finite induction. Conversely the property W whose root extension consists exactly of these numeral denotations, with any profile (say top), is admitted. It contains zero and is successor-closed at o; the impredicative definition of N_e therefore restricts N_e to that extension. The numeral denotations are pairwise distinct: full finite components distinguish any two cardinality numerals, even though the actual individual domain is singleton.

Choose an external injection f:D_t(o)→N_e(o). The root relation R of type t ν_e t with actual extension the graph of f and bottom profile is admitted. At the root it witnesses Ctbl_(e,t)(top_t) in the exact background definition: two root propositions share an N_e-index iff they are identical. Hence

C + pure Maximalism + Ctbl_(e,t)(top_t)

is consistent. This is internal countability, not Countable Boolean Completeness. No implication from Strong Possibility to this countability statement has been proved here.

## 6. Other audited observations

Pure Maximalism implies the one-free-individual-variable instances of Possibility+. For a C-consistent pure P(x), make a singleton-root coalescence with a component witnessing P(a), carrying the sole root individual to a. At that root Q:=E_1∧∀x◇P(x) holds, so Q is C-consistent. At a pure-Max world, ◇Q holds. Any actual x transports into the unique individual of that Q-world, so ◇◇P(x), hence ◇P(x) by 4. Therefore pure SP, which forces E_1 by the recorded argument, implies all pure Possibility+: instances with at least two displayed distinct individuals have false antecedents.

More generally C proves ◇_≠ U→U for every universal sentence U=∀x̄ θ(x̄) whose matrix is a finite Boolean combination of typed term identities. Each equality is necessary if true; each disequality is □_≠-persistent by taking that disequality as the true witness in the definition and using NI. Finite truth-functional combinations of such literals are □_≠-persistent. An actual countertuple to U therefore remains a countertuple in the relevant distinctness-preserving sense, ruling out ◇_≠ U. This can also be proved directly from the definition with a finite conjunction of the countertuple's true identity/disequality literals. Thus pure SP entails every pure Max-consistent U in this fragment. Atom_t(A_n) belongs to it because algebraic ≤ is an identity of Boolean terms. Combining §§4 and 6 proves:

Pure SP ⇒ Atom_t(F∧E_n), for every n≥1.

No contradiction follows from these atom conclusions alone.

## 7. A pointed propositional-generation criterion for Strong Possibility

Original argument from the local-strengthening research subagent, audited here. Suppose M satisfies pure Maximalism and some actual individual a has this external property: every actual proposition is the denotation of a pure t-term Q(x) evaluated at a (Q has no free variable other than x). Then M satisfies pure Strong Possibility.

Proof. Fix a closed pure P with Max(C)+P consistent and an actual true proposition q. Write q=Q(a). Because Q(a) is true in a C-model, Q(x) is C-consistent. The unary Possibility+ theorem in §6 therefore makes ∀x◇Q(x) a consequence of pure Max. Hence Max(C)+P has a model in which P∧◇Q(x) holds of an individual, so that pure one-variable formula is C-consistent. Unary Possibility+ at M yields ∀x◇(P∧◇Q(x)), in particular ◇(P∧◇Q(a)). Since this holds for every true q, the dual definition gives ◇_≠P. This proves every pure SP instance.

Existence of the required model is NOT proved. It would suffice to omit, in a suitable countable model of pure Max with a distinguished individual a, the type {p≠T(a): T a pure t-term with at most the free individual variable x}. The required nonprincipality/omissibility has not been established. Naively restricting a model to term denotations does not preserve quantifier semantics.

The variant requiring CLOSED PURE terms (without the individual parameter) is impossible for Max, despite being a formally sufficient criterion. To see this, let A(x):=∀y(x=y∨□(x≠y)). In a full action model on the one-object idempotent monoid {1,k}, with individuals a,b,c and k(a)=k(b)=a,k(c)=c, A(c) holds and A(a) fails. Therefore for every closed pure Q, C cannot prove A(x)=Q, since that would make A uniform. The singleton-root argument underlying §6 makes pure Max entail ∀x A(x)≠Q. Thus every individual supplies a proposition outside the set of closed-pure-term denotations. This refutes the unpointed term-generation route, but does not refute the pointed criterion.

## 8. Actual atoms obstruct pointed propositional generation

Original additional theorem. In a model of pure Max, no true propositional atom is denoted by a pure term Q(a) with a single individual parameter. Consequently any model satisfying the sufficient generation condition of §7 must refute Actuality.

Suppose Q(a) is a true atom. For every pure Max axiom M, M is actually true, and a true Boolean atom entails each actual truth: otherwise its meet with ¬M would be a nonzero part, forcing Q(a)≤¬M and contradicting truth of both Q(a) and M. Thus □(Q(a)→M).

If C+Q(x)∧¬M were consistent, unary Possibility+ (§6) would give ◇(Q(a)∧¬M), a contradiction. Therefore C proves ∀x(Q(x)→M). The consistent recursively enumerable theory R:=C+∃x Q(x) contains every pure Max axiom.

No consistent recursively enumerable extension R of C can contain pure Max. For a closed pure identity I, dovetail a search for a C-proof of I and an R-proof of ¬I. If C proves I, consistency of R prevents the second search from succeeding. If C does not prove I, pure Max is contained in R, so the second search succeeds. This would decide C-provability of closed pure identities, and hence of arbitrary closed pure P because C proves P iff C proves P=top. C-theoremhood is undecidable: first-order validity reduces to it by replacing finitely many relation symbols with higher-order variables and universally closing those variables. A valid first-order sentence is provable already in H; an invalid one has a full extensional Henkin countermodel of C under a suitable relation assignment. Church's undecidability theorem supplies the contradiction.

Thus the pointed generation type in §7 is not nonprincipal over bare Max: the formula 'p is true and an atom' is consistent with Max (ordinary coalesced roots witness Actuality) and entails every inequality p≠T(a). This does not show the type cannot be omitted after adding ¬Actuality, nor does it refute Strong Possibility. It identifies a necessary restriction on that proposed construction route.

## 9. Pure Strong Possibility is incompatible with signature Maximalism

Original theorem, using the construction above rather than any conjectured signature conservativity. Let Σ be any admitted signature containing a relational constant c^τ, as the map assumes. Then

C + SP_pure + Max(C(Σ))

is inconsistent. This holds for every interpretation of the constants; it is not merely the observation that interpreting c as top spoils signature Maximalism.

Put A_1:=F∧E_1. By §4, Max(C)+Atom_t(A_1) is consistent. Atom_t(A_1) is a closed pure universal Boolean combination of term identities: use the equivalent Boolean-algebra formula

A_1≠bottom ∧ ∀p (p≤A_1 → (p=bottom∨p=A_1)),

and expand ≤ as an identity. The co-persistence lemma of §6 therefore shows C proves ◇_≠Atom_t(A_1)→Atom_t(A_1). Its Strong Possibility instance gives Atom_t(A_1).

Write τ=σ_1…σ_k t, possibly k=0, and define the closed Σ-sentence R(c):=∀x_1…x_k c[x_1,…,x_k], taking R(c)=c when k=0. In a full extensional model with exactly one individual, c can be interpreted as the top relation or the bottom relation. Every type domain is nonempty, so these interpretations make R(c) true and false respectively. Hence each of

A_1∧R(c),     A_1∧¬R(c)

is C(Σ)-consistent. Only TWO instances of signature Possibility Maximalism are needed: they imply both displayed propositions are nonbottom. They are disjoint subpropositions of A_1, contradicting its atomicity.

More generally pure SP implies the uniform finite splitter prohibition

∀p ¬(◇(A_1∧p) ∧ ◇(A_1∧¬p)).

Together with ◇A_1, already given by pure Max, this is equivalent to Atom_t(A_1). A candidate signature expansion is therefore already blocked by the two finite genericity requirements displayed above, without invoking all its Maximalism instances.

Consequences:

* No pure-SP model has an expansion satisfying signature Maximalism for any admitted Σ; a specially chosen 'separated' expansion cannot bypass this obstruction.
* Pure SP→signature SP is derivable over C iff pure SP is inconsistent: the forward direction conflicts with the present theorem, since signature SP implies signature Max; the reverse is explosion.
* Signature SP→pure SP is derivable over C iff signature SP is inconsistent, for the same reason. Thus the two proposed lift arrows are each consistency questions, for different theories.
* Max(C(Σ)) is not conservative over pure Max for pure sentences, for EVERY admitted Σ: Atom_t(A_1) is consistent with pure Max but inconsistent with signature Max. This is stronger than the elementary E_1 counterexample, which requires at least two individual constants.

These are semantic/syntactic inconsistency arguments using proved construction facts. They do not prove either pure SP or signature SP inconsistent separately.

## 10. Finite and infinite individual-parameter variants

Replace the singleton root by any nonempty set E. Give the root an arrow (V,I) for each component object V and assignment I:E→D_e(V), sending each b∈E to I(b). Profiles are pure terms in finitely many individual parameters labelled by E. The root relational domains remain arbitrary actual extensions paired with these profiles. The same closure and Maximalism proof works.

If |E|=m<∞, enumerate E by a_1,…,a_m. For a partition π of {1,…,m}, let δ_π assert that a_i=a_j exactly for pairs in the same block. At any finite extensional n-individual world, tuples are in the same automorphism orbit iff they have the same equality partition. Therefore A_n∧δ_π is an atom exactly for the partitions with at most n blocks, and these atoms form a disjoint exhaustive decomposition of A_n. Its number of atoms is Σ_{k=1}^{min(m,n)} S(m,k), where S(m,k) is a Stirling number of the second kind. This is a model calculation; it is not asserted to follow from Max alone.

If E is infinite, A_1 remains an atom. Every A_n for n≥2 is atomless in this root Boolean algebra. Indeed a nonzero p≤A_n has a profile using only finitely many individual parameters S. Choose fresh c outside S and an anchor d distinct as a parameter symbol from c (in S if possible, otherwise another fresh symbol). At a finite n-world realizing p's profile, extend the assignment first with c=d and then with c≠d, preserving the values of S. Both extensions exist because n≥2. Thus p∧(c=d) and p∧(c≠d) are nonzero proper parts of p.

For arbitrary E, the proposition domain has cardinal max(|E|,aleph_0): the upper bound counts finite syntax and parameters; E_n gives the countably infinite lower bound; for infinite E the profiles c=d for varying c and a fixed d separate in two-individual components, giving the |E| lower bound. For finite or countably infinite E, the internal countability proof of §5 still works. For infinite E, arbitrary actual extensions additionally provide an internal relation bijecting e and t whenever their external cardinalities agree, as they do here. None of these conclusions identifies Countable Boolean Completeness with countability.

## 11. Finite signatures: the atomic decomposition forced by signature SP

This section assumes Σ is finite. Individual constants, if present, are allowed; all have the unique value at an A_1-world. List its relational constants as c_1,…,c_r, of types τ_1,…,τ_r.

In the full singleton extensional model, each relational type τ has a finite nonempty domain D_τ^1, and every element has a closed pure term representative. This is proved by induction on type. The two propositions are bottom and top. At an e-input type there is one argument and every operation is represented by a constant function. At a relational input type there are finitely many pure-named arguments and outputs, and lambda abstraction with finite equality case distinctions represents every function. Output types are relational, so their pointwise Boolean combinations are admitted.

For every tuple d=(d_1,…,d_r) of possible constant values choose pure representatives T_(i,d_i) and put

B_d := A_1 ∧ ⋀_{i=1}^r (c_i=T_(i,d_i)).

At A_1-worlds these are exactly the distinct full Σ-interpretation diagrams. C(Σ) proves they are pairwise disjoint and their finite join is A_1. Each B_d is C(Σ)-consistent, so signature Max makes every B_d nonbottom.

Construct the profile root using L(Σ)-term profiles and components complete for C(Σ), with all interpretations. If Σ has individual constants, take the root individuals to be their distinct symbols and let each interpretation arrow send a constant to its interpretation; if none exist, use the singleton root with the extra individual marker as above. Interpret every relational constant by its own term profile and an arbitrary actual extension. The same closure proof verifies C and signature Max. At a B_d-world, the entire local finite extensional structure and every signature constant are specified. Every root individual marker also has the sole individual value. Thus each profile has one fixed truth value on all B_d-arrows. Since A_1 is actually false at this maximalist root, the atom proof of §4 gives Atom_t(B_d), simultaneously for all d.

Consequently each B_d is atomic under signature SP, by applying its metalinguistic side condition to the just-proved Max(C(Σ))-consistent sentence Atom_t(B_d), then universal-identity co-persistence. Hence signature SP forces A_1 to have exactly

N_Σ = ∏_{i=1}^r |D_(τ_i)^1|

atoms below it. At least one relational constant makes N_Σ≥2. Examples: one propositional constant gives two atoms A_1∧c and A_1∧¬c; one constant of type tt gives four atoms corresponding to the four Boolean unary functions.

This is consistent at the level of the corresponding atomicity constraints, by the constructed signature-Max model. It does not establish consistency of full signature SP. It explains the incompatibility in §9: pure SP forces one atom below A_1, whereas each nonempty finite relational signature forces a strictly finer finite atomic decomposition under its own SP. For infinite Σ, this finite full-diagram argument does not apply; no infinitary diagram is silently admitted.

## 12. Exact criterion for atomic closed propositions under pure Max and pure SP

Let A be a closed pure sentence and let a be a fresh individual constant. Say A is pointed-complete when C(a)+A is consistent and complete for closed sentences of the language with a. Equivalently C+A is consistent and, for every pure P(x) whose sole possible free variable is an individual x, C proves A→∀xP(x) or A→∀x¬P(x).

Then:

(1) Max(C)+Atom_t(A) is consistent iff A is pointed-complete.

(2) Pure SP entails Atom_t(A) iff A is pointed-complete; if A is not pointed-complete, pure Max already entails ¬Atom_t(A).

Here the 'iff' in (2) is the classification supplied by the proofs, under the standing conditional consistency of pure SP; no assertion of SP consistency is smuggled into a claim about formal entailment. More precisely, pointed-completeness yields an SP proof of Atom(A), and failure yields a Max proof of its negation. If SP itself is inconsistent it proves both, so an unqualified syntactic biconditional about which formulas it proves would be misleading.

Necessity and the negative classification. If C+A is inconsistent, A is bottom. Otherwise, if pointed completeness fails, some P(x) makes both A∧P(x) and A∧¬P(x) C-consistent. Unary Possibility+ gives, for any actual individual b, nonzero propositions A∧P(b) and A∧¬P(b). These disjoint parts refute Atom(A). Thus every Max-model refutes its atomicity.

Sufficiency. In the singleton profile root of §§1–3, a proposition has some pure one-individual-variable profile T(z). Pointed completeness makes its profile either uniformly true or uniformly false at all A-arrows. Thus p∧A has profile either A or bottom. Also A is actually false at this root. For if A were true, the complete consistent theory C+A would prove every pure Max axiom: it decides each such axiom, and its negation is impossible because this root satisfies A and Max. This contradicts §8's theorem that no consistent r.e. extension of C contains pure Max. Hence p∧A has actual coordinate false, and so is genuinely either A or bottom as a pair. The profile of A is nonbottom by C-consistency and source completeness. Therefore A is an atom. Finally Atom(A) is universal in term identities, so its Max-consistency plus SP gives its actuality by co-persistence.

The same proof works for a relational-only nonlogical signature Σ: replace pure formulas by Σ-formulas and use unary Possibility+Σ, proved by the singleton-root argument (there are no individual constants for the antecedent to exclude). If Σ contains individual constants, an alternative profile root has exactly those constant symbols as its actual individuals and uses closed Σ-term profiles, with no dummy marker. In that setting ordinary completeness of C(Σ)+A, rather than pointed completeness, is sufficient and necessary for Max(C(Σ))+Atom(A) consistency. For the r.e. obstruction, only the finite sublanguage occurring in A is needed: unused extra constants are conservative over C, so a finite-language r.e. theory would already contain the pure Max axioms.

Caution: for a relational-only signature, mere completeness of C(Σ)+A is not enough. A complete finite extensional Σ-structure can have several orbits of individuals under its automorphism group. A Σ-formula P(x) distinguishing two orbits then splits A, by unary Possibility+Σ. At a singleton extensional structure there is exactly one orbit, which is why §11 works without this complication.

## 13. Arbitrary independent atomic-versus-atomless choices

Original theorem (finite-generator independence suggested independently by the local-strengthening subagent). For every external subset S of the positive integers there is a pure-Max model whose propositional Boolean algebra makes A_n atomic exactly when n belongs to S, and makes A_n atomless whenever n does not belong to S. These models still have internally countably many propositions. The language and the reference theory C remain pure and unchanged.

Construction. For each n outside S introduce countably many auxiliary propositional profile symbols d_(n,j), j∈N. For every pure component in the construction of §1 take all its expansions in which, independently for each pair (n,j), d_(n,j) denotes either the pure proposition A_n or bottom. The auxiliary symbols are only devices for defining the semantic root domains: the resulting model is finally taken in the PURE reduct, and signature Maximalism for them is neither imposed nor claimed. Profiles are now terms T(z,d_1,…,d_k) using finitely many auxiliary symbols. There are countably many such terms. Root domains remain arbitrary actual extensions paired with these profiles. The same substitution proof verifies term closure, H and Logical Equivalence; all original pure components remain represented, so pure Max holds.

If m∈S, every auxiliary d_(n,j) is bottom as an entity at every A_m-world: n≠m, so A_n is false there, and F identifies every false proposition with bottom. Thus every profile has the same truth at all pointed A_m-worlds, by the finite extensional uniqueness argument of §4. A_m is actually false and nonbottom, so it is an atom.

If n∉S, let p be a nonzero subproposition of A_n. Its actual coordinate is false, since A_n is false at the root. Choose a profile T(z,d_1,…,d_k) for p and a fresh symbol d_(n,j) not occurring in it. Since p is nonzero, there is a component arrow realizing its profile truly; p≤A_n makes its target an A_n-world. Keeping the underlying pure component and every auxiliary in T fixed, take two expansions differing only in the fresh symbol, interpreting it as A_n and as bottom. The value of T is unchanged in both expansions. Let r be any root proposition having profile d_(n,j). Then p∧r and p∧¬r have true profiles respectively on the two arrows. They are disjoint nonzero parts of p. Hence no nonzero part of A_n is an atom: A_n is atomless.

Countability follows from countable finite syntax and the free actual truth bit, exactly as in §5; the arbitrary root relation domains still provide the internal injection into standard cardinality numerals. Consequently each of the countably many natural pure unboxed assertions Atom(A_n) is independently choosable over pure Max, even while retaining internal countability. This proves relative consistency and nonimplication claims; it does not assert any particular SP-consistency result. The stronger atomless alternative contains existential splitting and is not itself one of the universal-identity formulas reflected by §6.

The specialization S=positive integers gives the original profile root. A direct simpler countermodel to Atom(A_n), without any auxiliary-language bookkeeping, is ordinary full coalescence with two distinct copies of a full finite n-individual component: arbitrary root proposition extensions across the copies separate them and split A_n. Thus strictness of the atomic strengthening never depends on assuming a signature-conservativity principle.

Caution. This argument relies on the finite Fregean cells: A_m-worlds identify every false A_n with the bottom entity. It does not establish arbitrary atomicity patterns for an arbitrary collection of merely disjoint pointed-complete formulas. Mere falsity at a non-Fregean world need not identify a proposition with bottom.

## 14. Finite-signature extension obstruction

Let Σ⊊Σ' be finite signatures with at least one relational constant newly added in Σ'. Then SP_Σ is incompatible with Max(C(Σ')). Choose any singleton full extensional interpretation of the old signature and let B be its complete old-signature diagram conjoined with A_1, as in §11. Signature SP_Σ forces Atom(B). A newly added relational constant d may independently be interpreted as top or bottom while retaining B. For R(d):=∀x̄ d[x̄], both B∧R(d) and B∧¬R(d) are C(Σ')-consistent. Two instances of Max(C(Σ')) make both nonzero, splitting B. Thus the reference language in SP is mathematically decisive at every such finite extension, not just at the pure-to-signature boundary. This does not prohibit nongeneric signature expansions and does not prove any one fixed-signature SP inconsistent.

## 15. Finite rigid Boolean-valued cells: non-Fregean pointed-complete theories

Original construction and theorem, independently audited by the local-strengthening subagent. For positive integers n,k let E_m^σ say that type σ has exactly m entities, let ND_σ abbreviate ∀x^σ y^σ(x≠y→□(x≠y)), and set

B_(n,k) := □(E_n^e ∧ E_(2^k)^t ∧ ND_e ∧ ND_t).

Then B_(n,k) is C-consistent and pointed-complete in the sense of §12. Consequently pure Max+Atom(B_(n,k)) is consistent, and pure SP entails Atom(B_(n,k)), for every n,k. For k>1 these are non-Fregean cells, so the finite Fregean A_n do not exhaust the consistently atomic closed pure propositions.

Existence. Take k mutually accessible worlds, with the same n-element individual domain at each. Propositions are all subsets of the k-world set. At every relational function type use ALL functions from the corresponding finite input domains into the proposition Boolean algebra. Transport all entities identically between worlds. The truth map at a world tests membership of that world; equality is crisp (top for identical entities, bottom otherwise), application is function evaluation, connectives are Boolean operations, and quantifiers are finite meets/joins. This full constant-domain rigid S5 action model validates H and Logical Equivalence. It satisfies B_(n,k) at every world.

Uniqueness and completeness. Consider any action-model world satisfying B_(n,k), and all its reachable worlds. The e- and t-transports are injective by boxed ND and have equal finite source and target cardinalities, so are bijective. Induct simultaneously over relational types at every reachable world. If all input and output transports are bijective, a relation is determined by its actual function: agreement of its values on actual inputs is preserved by NI, and every future input is the transport of an actual input, so the two entire intensions agree. Thus Functionality holds at this type: the entity is determined by its identity-valued applicative behavior. This is NOT Extensionality by actual truth coextension, which fails when k>1. Conversely every function on the finite input domain into the finite output domain is represented by finite lambda case distinctions, because lower-type equalities are crisp. Every such function therefore occurs. Its transport is conjugation by the lower-type bijections and is consequently bijective. This establishes the induction, including rigidity of equality at every type.

The resulting local typed algebra is uniquely the full finite function hierarchy on an n-element individual set and a Boolean algebra with 2^k elements. Its logical operations and quantifiers are fixed by Boolean operations, crisp identity and finite meets. The actual truth map is one of the k Boolean ultrafilters. Every permutation of the individuals and every permutation of the k Boolean atoms extends recursively to an automorphism of the entire typed algebra. These automorphisms are transitive on pairs consisting of a truth ultrafilter and an individual marker. Hence every pure formula P(x) has one fixed truth value in all B_(n,k)-worlds, independently of the chosen individual. Semantic completeness for C gives precisely pointed completeness.

For k=1, B_(n,1) is C-equivalent to A_n=F∧E_n. At a Fregean world every actual truth is top and therefore necessary; in particular its finite individual cardinality and base-type ND facts persist, giving B_(n,1). Conversely a two-element proposition domain gives F.

The independent-choice construction of §13 extends to the countable family {B_(n,k):n,k≥1}. For different pairs the cells are disjoint, and each is bottom AS AN ENTITY at every world of another cell: their boxed incompatible base cardinalities make them impossible there. Auxiliary selectors assigned a cell or bottom therefore disappear completely at protected cells, while fresh selectors split every nonzero part of an unprotected cell. Thus arbitrary atomic/atomless choices for all finite rigid cells are simultaneously compatible with pure Max and internal countability. This extension keeps the reference language and C unchanged; auxiliary symbols are removed in the pure reduct.

## 16. Finite relational signatures: pointed finite-structure atom counts

Original refinement from the local-strengthening subagent, audited here. Let Σ be finite and contain only relational nonlogical constants. Fix n≥1. There are finitely many full n-individual extensional Σ-structures up to isomorphism. For each such structure M, let D_M be its complete finite Σ-diagram conjoined with A_n, and let O_(M,1)(x),…,O_(M,r_M)(x) define its individual automorphism orbits. Finite diagrams and orbit formulas exist: existentially enumerate the n individuals, use finite lambda truth tables to name every higher-type value, give the tables for the finitely many constants, and specify the distinguished individual's enumeration position. All relevant type domains are finite under F∧E_n.

In the singleton Σ-profile root, each D_M∧O_(M,i)(a) is an atom, for the root's individual a. Every profile is uniform over that complete pointed structure, and A_n is false at all new root coordinates. Thus Max(C(Σ)) is consistent with the universal identity sentence ∀a Atom(D_M∧O_(M,i)(a)). Signature SP forces each of these sentences by reflection. For a fixed actual individual a, their pieces are disjoint and join A_n; their nonzeroness also follows directly from unary signature Possibility+. Consequently SP_Σ makes A_n have exactly

N_Σ(n) = sum_M r_M

atoms. Equivalently this is the number of isomorphism classes of pointed full n-individual Σ-structures, or the number of S_(n−1)-orbits on the finite set of all interpretations of Σ on a fixed n-element domain with a distinguished individual. These atomic-decomposition constraints for every n coexist in the signature profile model; they do not prove full signature SP consistent.

Examples. One propositional constant gives N_Σ(n)=2. One unary individual-predicate constant gives N_Σ(n)=2n: classify by its extension size and whether the distinguished individual belongs (one option at sizes 0,n and two at intermediate sizes). The singleton formula of §11 is the special case n=1.

If Σ instead has named individual constants, use the closed-Σ-profile root from §12. Its relevant finite atoms are complete UNPOINTED Σ-structure diagrams, because every root individual is already a named constant. The extra anonymous-point orbit split used above is specific to the relational-only case.

## 17. Stronger obstruction to the naive omitting-types construction

Original observation from the local-strengthening subagent. Merely adding ¬Actuality, even together with E_1, does not make the full pointed-generation type of §7 nonprincipal. There are Max+E_1+¬Actuality models in which A_1 is atomless (the finitely supported substitution/root constructions described in the companion notes supply them). Hence the formula θ(p):=(bottom<p<A_1) is consistent over that theory.

For every pure one-individual-variable term T(x), pointed completeness of A_1 makes C prove A_1≤T(x) or A_1≤¬T(x). In either case T(a) cannot be a nonzero proper part of A_1. Thus θ(p) entails p≠T(a) for every such T, and locally isolates the entire 'not denoted by any pointed pure term' type. The same obstruction arises from a proper split of any pointed-complete cell. A viable whole-term-generation omitting-types argument must impose at least the canonical atom laws, rather than merely excluding Actuality. These laws are all simultaneously satisfied in the original profile root.

This obstruction does not apply directly to the weaker named-TRUE-neighborhood criterion: θ(p) makes p actually false at a Max world, since A_1 is actually false there. Whether the true-neighborhood condition can be realized remains unresolved here.

## 18. Arithmetic boundary on isolated complete cells

Original deduction from the local-strengthening subagent using the recorded Fregean arithmetic lemmas. If A is a consistent pointed-complete closed pure sentence, then C proves A→¬I_σ, for every fixed type σ to which those arithmetic lemmas apply. Indeed, if A∧I_σ were consistent, ordinary completeness of C+A would force I_σ. The arithmetical consequences of the consistent r.e. theory C+A would then be a complete consistent r.e. extension of PA, contradicting Gödel–Rosser incompleteness. The relevant arithmetic source boundary is documented in .reproduction/classicism-research/infinitary-standard-numerals-20261022.md §1.

This gives a necessary boundary for the complete-cell classification; it does not prove that every such cell is one of the finite rigid B_(n,k). Internal failure of I_σ does not by itself establish external finiteness of the typed domain, and nonstandard finite truncations must not be silently excluded.

## 19. Retract constructions giving substantial Strong-Possibility fragments

The independently audited companion .reproduction/classicism-research/reflection-retract-fragments-20261022.md gives a stronger use of profile roots. Its §8 combines a singleton-marker root R with a finitely supported generic target W, adding a unique arrow a:R→W and return arrows b:W→R satisfying ba=id_R. The root retains pure one-individual old profiles. W has infinitely many free generators at every type, with substitutions fixing the marker, and is a pure-Max model satisfying the whole Barcan schema and propositional atomlessness. R retains Actuality, all canonical complete-cell atoms, and internal countability of propositions. The retractions make every true root proposition remain possible at W; hence R satisfies D of every finite conjunction of the verified W-properties, including any finite list of Barcan instances, despite their failure at R where proved elsewhere. Here D means ◇_≠.

The BF proof has three separate cases: an old-target witness is lifted with a fresh interpreted generator; a W-self-arrow witness is lifted by moving its finite support to fresh generators and choosing a reverse substitution; a return-arrow witness y∈R is lifted by the already available entity a(y), because b(a(y))=y. Thus no self-referential naming of all root entities is needed. Free individual generators at W give the e-case while preserving the singleton root.

A related finite-pattern graft uses a finite collection of targets W_S, with generators d_(cell,j) only for cells prescribed atomless there, interpreted at old targets as their cell or bottom. Here the patterned cells are restricted to the necessarily incompatible boxed rigid family B_(n,k) of §15 (including A_n), or another family for which that same necessary incompatibility has actually been proved. Distinct arbitrary pointed-complete cells are not sufficient; §21 supplies a counterexample. Cross-arrows substitute a source generator by a same-cell target generator if present, or by the logical cell or bottom. This keeps the category closed under composition, including returns through R. Every W_S realizes its prescribed atomic/atomless pattern by §13's argument. R keeps all canonical cells atomic and satisfies D of each prescribed pattern separately. With finitely many targets its proposition domain is still countable (finitely many actual truth coordinates and countably many old profiles), so internal countability is retained. This establishes consistency of every finite collection of these SP instances together with the atom laws; it does not assert D of a conjunction of mutually incompatible patterns, or consistency of full SP.

The two grafts in this section can be combined safely, provided the Barcan target has an infinite reserve of generators in EVERY restricted cell-family used at any pattern target, in addition to its unrestricted generators of every type. Restricted generators may map to a generator of the same family, its logical cell, or bottom. Unrestricted generators may map to any target generator of the same type or to the admitted fixed logical terms (including the cells, as needed for composition). The old interpretations of restricted generators remain cell-or-bottom; no arbitrary-term substitution machinery is needed.

For a witness y at any new target, move its finite generator support, family by family, into fresh generators of the Barcan source outside the finite support of F. Choose a reverse substitution agreeing with the original arrow on F's support and sending those fresh generators back. Its composite fixes y's support, so the renamed actual source entity witnesses BF. At the singleton root use the section a(y), as above; at old targets use an unrestricted fresh generator. This is the additional case needed to retain BF after adding restricted pattern targets. Omitting those reserves would leave a genuine gap in the original three-case BF argument.

Thus one finite graft simultaneously retains root Actuality, internal countability, all canonical complete-cell atom laws, D of every requested target pattern separately, and D of every verified finite conjunction at the all-type-Barcan/atomless target. In particular it realizes any finite collection of the canonical atomic/atomless-pattern SP instances together with these Barcan-target SP instances. It does not assert D(BF∧a protected atomic pattern); that conjunction need not be Max-consistent.

## 20. Stronger finite-bound theorem for complete cells

The arithmetic boundary of §18 has now been strengthened. The detailed, independently audited proof is .reproduction/classicism-research/complete-theories-finite-bounds-20261022.md. It proves: if T is a consistent r.e. extension of C, complete for closed pure sentences, then for every type σ there is an external standard integer b such that T proves □¬AtLeast_b(σ). The theorem requires only ordinary pure completeness, so applies in particular to every pointed-complete cell.

The new ingredient interprets Robinson's essentially undecidable theory R in C plus the schema of every standard actual size lower bound at σ. Bounded-standard predecessor uniqueness follows from the recorded finite-cardinality exclusivity lemma. Finite-prefix inductive relations make Sum and Prod uniquely correct on standard inputs. Definable default-to-zero graphs supply total first-order arithmetic operations without requiring any admitted choice operation. The primitive order relation ∃k∈N Sum(m,k,n) satisfies R's bounded-prefix and comparison schemata. Completeness would therefore contradict R's essential undecidability unless some standard finite bound held. Applying that argument to the cardinality type ν_σ yields a finite disjunction of standard numeral collisions; NI and finite-cardinal separation turn every disjunct into the same necessary finite bound on σ.

No optional premise is necessitated. The result does not imply rigidity, and it does not classify all complete cells as B_(n,k). Finite nonrigid transports remain a genuine possibility.

## 21. Finite Barcan reconstruction and a nonrigid pointed-complete cell

The detailed proof is .reproduction/classicism-research/finite-base-barcan-chain-20261022.md, developed by the construction and local-strengthening subagents and independently audited here. Finite actual e and t domains, together with BF_e and BF_t, force both base transports onto every future domain. Induction over relational types then gives finite domains, surjective transports, and Functionality at every type throughout the generated cone. The higher domains are exactly the finite tables satisfying delta_sigma(a_i,a_j) <= delta_tau(p_i,p_j); finite lambda interpolation realizes every compatible table. When lifting a target table, arbitrary source lifts need not be compatible at the source: interpolation is required to recover only the compatible transported target table. Equalities and quantifiers become finite meets, so the finite e-equality matrix, the finite propositional Boolean/modal table and the actual truth ultrafilter reconstruct the entire local typed logical algebra.

Consequently a realizable finite diagram of these base data, conjoined with BF_e and BF_t, is complete over C. With a singleton individual domain it is pointed-complete. In particular, let

A_chain := E_1^e and E_4^t and BF_e and BF_t and exists p^t [p and Atom(p) and Box(p)=bottom and Box(not p)=not p].

This has the full two-world coalescence model r→s, with singleton individuals at both worlds and propositional domains of size 4→2. The propositional algebra at r is {bottom,p,not p,top}, where p={r}; Box(p)=bottom and Box(not p)=not p. The full higher domains have, for example, size 64→4 at tt. The fixed finite base table and the reconstruction theorem establish pointed completeness of C+A_chain.

Computing the Fregean Axiom by the reconstructed finite quantifier table gives F=not p AS AN ENTITY at every A_chain world. The singleton-individual sentence is top, so A_1=not p. Thus C proves A_chain→(Diamond A_1 and not A_1). Distinct pointed-complete cells therefore need not be necessarily incompatible. This is a counterexample to extending the independent-pattern construction solely on the basis of distinct pointed completeness, and to classifying every complete cell as a finite rigid B_(n,k). It is not a claim about the map's separately named Separated Structure principle.

The atom criterion still applies without alteration: pure Max+Atom(A_chain) is consistent, the profile root realizes this atom together with every other pointed-complete-cell atom, and pure SP entails Atom(A_chain). No Extensionality claim is made; the reconstruction establishes Functionality.

## 22. Complete cells can fail either or both base-type Barcan sentences

Two further independently audited notes settle the question left open after §21. The first is .reproduction/classicism-research/finite-coalescence-bf-e-failure-20261022.md. Let L_n describe a four-proposition chain root with one actual individual, BF_t, singleton individuals at its rootlike successors and Fregean n-individual leaflike successors. Its exact finite formula is equation (1) of that note. At every type, a root entity is determined by its actual extension and its value at one leaf. The corresponding domain is exactly the product of all actual extensions and its allowed leaf profiles. For n=2 every relational leaf entity is named by a pure term in the root individual's image: the other individual is the unique x unequal to that marker, so no individual-valued choice term is required. Hence L_2 isolates the full coalescence and is pointed-complete. For general n, adding the maximum unary-predicate cardinality E_(2^(n+1))^(et) forces every leaf singleton profile, which in turn names every relational profile and yields a pointed-complete cell C_n. All n>=2 examples refute BF_e, using the predicate x=a. The bare L_3 is incomplete: unrestricted leaf profiles give 16 root unary predicates; profiles fixed by the swap of the two unmarked individuals give 8.

The second note is .reproduction/classicism-research/finite-complete-cell-failing-barcan-t-20261022.md. Its A_swap has a singleton root and a four-element chain propositional algebra, with boxed singleton/four-proposition rootlike successors and boxed B_(1,2) leaflike successors. It does not assume BF_t. Every leaf image of a root proposition is bottom or top. A non-invariant relational leaf profile would select one of the leaf's two Boolean atoms by a pure term, contradicting that restricted image. Conversely every atom-swap-invariant profile has a pure term name, obtained by symmetrizing over the two atoms. Thus the whole root hierarchy is reconstructed as arbitrary actual extensions paired with exactly the invariant leaf profiles, establishing pointed completeness. Here the swap is an automorphism of the typed logical algebra WITHOUT its chosen actual-truth ultrafilter; it preserves term denotations and exchanges the two truth worlds. A_swap refutes BF_t explicitly, and also refutes Functionality_tt.

Replacing the leaf B_(1,2) by B_(2,2) gives A_mix. The root marker distinguishes the two leaf individuals, while the same atom-swap argument handles the two propositional atoms. The reconstruction again establishes pointed completeness, and both BF_e and BF_t fail. Accordingly all four combinations of the two base Barcan sentences occur in finite pointed-complete cells: A_chain has both; L_2 has only BF_t; A_swap has only BF_e; and A_mix has neither. Their corresponding atomicity assertions are all simultaneously Max-consistent and all consequences of pure SP by the general criterion. This is a construction theorem, not a claim that complete cells or pure SP have been fully classified.

## 23. A finite-group classification of the specified rigid-leaf chain family

The unified referee proof is .reproduction/classicism-research/finite-rigid-leaf-galois-classification-20261022.md, independently audited here. For positive n,k, let L_(n,k) assert a singleton actual individual domain, exactly four actual propositions, and an actual true atom p with Box(p)=bottom and Box(not p)=not p. Add Box(p→(E_1^e and E_4^t)) and Box(not p→B_(n,k)). No Barcan premise is included.

Every such world's relational domains have the form arbitrary actual extensions paired with the fixed entities of one subgroup H≤Sym(n−1)×Sym(k) in the finite rigid leaf hierarchy. The first factor fixes the transported root individual; the second permutes the Boolean atoms. H must be transitive on those atoms because the transported root propositions are exactly bottom and top. Conversely every such subgroup yields a model. The proof is finite definability: finitely many allowed profiles already have their common stabilizer H; existentially enumerate the leaf individuals and Boolean atoms, match those parameter tables, and join the desired H-fixed output. Every matching enumeration differs by H, so the output is constant as an entity and is forced into the allowed profile family.

The subgroups are classified up to conjugacy. Each conjugacy class has an explicit finite pure isolator J_(n,k,H), using a root relation whose leaf profile is the characteristic relation of an H-orbit of a complete individual/Boolean-atom frame. The defining clause uses ENTITY identity of relations, not actual truth coextension. A finite conjunction excluding every proper-subgroup orbit case isolates the conjugacy class. Hence L_(n,k) has exactly as many complete pointed cells as there are such transitive subgroup conjugacy classes. This is a classification of the displayed two-region condition, not of all complete C-extensions.

For k=1 the condition recovers the Fregean-leaf family of §22 and the groups are subgroups of Sym(n−1). Thus L_(3,1) has two complete cells and L_(4,1) has four. For n=1,k=3 the two classes are the cyclic group of order three and Sym(3); their root tt-domains have respectively 4096 and 1024 entities, despite identical e,t base data. The elementary n,k≤2 cases recover all four base-Barcan combinations from §22.

All inequivalent cells J_(n,k,H), across this entire countable family, are necessarily incompatible with each other. A rootlike arrow preserves every source proposition's truth and therefore retains its complete cell; a leaflike target is rigid and cannot satisfy any chain cell. Thus every foreign chain cell is bottom as an entity. The independent atomic/atomless pattern construction of §§13 and 19 consequently applies to this countable family alone. It must not be mixed indiscriminately with the rigid B_(n,k) cells, since a chain cell accesses its own rigid leaf cell.

If c(n,k) is the finite number of the indicated subgroup conjugacy classes, pure SP makes L_(n,k) the join of exactly c(n,k) propositional atoms: the finite complete-cell decomposition is a C-theorem, Max makes each consistent cell nonzero, and SP makes each cell an atom. The original profile root realizes all these minimum finite widths simultaneously, together with internal countability. Pure Max alone already forces at least that many disjoint nonzero parts, but permits any of these parts to be atomless by the independent-pattern construction.

## 24. Barcan is equivalent to each corresponding Functionality sentence

The exact proof is §10 of .reproduction/classicism-research/finite-rigid-leaf-galois-classification-20261022.md. For every input type sigma and relational output tau, C proves BF_sigma iff Functionality_(sigma→tau). This is a general C theorem, not restricted to the finite constructions. The equivalence of the FULL SCHEMATA is already derived in the proved local map: Functionality implies Tractarianism, which implies BF, and the forward BF-to-Functionality implication is directly recorded. The contribution here is a direct proof at each fixed input/output pair. No claim of literature novelty is made.

Forward, pointwise identity becomes necessarily pointwise identity by NI; BF_sigma moves that one input quantifier under the box; C's modalized Functionality identifies the operations. Reverse at output t, the BF premise forall x Box(Xx) is exactly forall x Xx=top. Functionality gives X=(lambda x top). Applying the universal-quantifier term to that identity gives (forall x Xx)=top, which is the BF conclusion. A general relational output tau reduces to t by the constant-relation embedding p↦lambda z_bar p and its application retraction; only finitely many arbitrary arguments from nonempty types are used, and no optional assumption is necessitated.

The unified finite classification therefore determines every input/output Functionality instance as well as every BF instance. In J_(n,k,H), BF_e holds exactly when n=1. At a relational input type containing only t, BF holds exactly when k=1. At a relational input type containing an occurrence of e, BF holds exactly when H is trivial. The proof uses finite-source BF iff every outgoing transport is onto, image Fix_H at relational leaf types, and the full-function-space action-kernel identity ker_(sigma→tau)=ker_sigma intersect ker_tau.

In particular the complete finite cell A_mix with n=k=2 refutes BF at every type and Functionality at every admitted input/output pair. A direct witness in any failed input type is g(x)=b and not(bigvee_i x=a_i), where the a_i enumerate the finite current domain and b is the leaf region. It is bottom on every current argument as an entity, yet top at a missing leaf argument. Constant-relation lifting supplies the witness for every relational output type.

## 25. Arbitrary mixed patterns across chain cells and their rigid leaves

The stronger independently audited construction is .reproduction/classicism-research/mixed-chain-leaf-atom-patterns-20261022.md. It proves that arbitrary atomic/atomless choices on the UNION of all chain cells J_(n,k,H) and all rigid cells B_(n,k) are simultaneously compatible with pure Max, internal countability and the profile root's actual atom. In particular pure Max+Atom(J_(n,k,H)) is consistent with the entire interval below its own possible leaf B_(n,k) being atomless, and the converse pattern is consistent too. This uses a new construction, not an inference that these mutually accessible cells are necessarily incompatible.

For an unprotected chain K, add countably many selector constants d<=K. For an unprotected leaf B, add countably many d<=B, and globally require each such d to be bottom AS AN ENTITY at every protected chain world. Use a fixed C-complete set of underlying components, all its allowed selector expansions, and all standalone full finite rigid components with their allowed expansions. All-bottom expansions preserve pure Max. At a protected cell all selectors are bottom, so every profile reduces to a pure one-individual term and pointed completeness gives atomicity.

An unprotected chain interval splits by changing a fresh selector to bottom or its chain cell. For an unprotected leaf interval, copy the finite term profile of a nonzero witness into a standalone full rigid B component, preserving its marker, current truth atom and the finitely many selector values. All protected-chain conditions are vacuous there, because no chain cell is possible in a rigid leaf component. A fresh B-selector can therefore be bottom or top while the finite witness profile stays true. This splits every nonzero part of B and proves atomlessness. Existing selector values may be arbitrary subpropositions; restricting every selector to only bottom or the whole cell would not supply this replication argument as stated.

The original restriction in §19 remains the correct scope of that particular mutual-exclusion graft. Extending the retract construction to the mixed-pattern model needs its own family-specific substitution argument: a leaf selector forced to vanish on a protected chain cannot generally be replaced by the logical leaf cell. That additional argument is kept in the separate reflection-retract note and summarized in §26, rather than silently inferred here. Full Strong Possibility remains unresolved.

## 26. Finite Strong-Possibility fragments for the mixed patterns

The separate reflection lane has independently audited and recorded the required constrained-family retract construction in .reproduction/classicism-research/reflection-retract-fragments-20261022.md §13. It extends the finite mixed-pattern consistency result of §25 to the substantial SP fragments of §19.

A restricted leaf-generator family records both its leaf B and the protected-chain set. At an old target its admissible values are q<=B satisfying Box(J→q=bottom) for every protected chain J. These conditions are stable under forward transport and always admit bottom. New substitutions send a restricted generator ONLY to another generator of the same family or bottom; in particular they do not send it to the logical B when that would violate a protected-chain condition. Return maps to the singleton root send restricted generators to bottom. These maps compose, and every return remains a retraction of the unique root-to-target arrow.

The Barcan target has an infinite reservoir in every constrained family, as well as unrestricted generators at all types. Its finite-support renaming and reverse-substitution proof therefore handles witnesses at every new pattern target. Old-target witnesses use unrestricted fresh generators. The standalone-B replication argument proves each pattern target's unprotected leaf intervals atomless, while protected intervals stay atomic. With finitely many new target objects, the root still has finitely many new truth coordinates and countably many pure old profiles, retaining internal countability and all canonical complete-cell atoms.

Consequently every finite collection of the mixed chain-and-leaf atomic/atomless-pattern SP instances can coexist with the verified Barcan/atomless/uncountable-target SP instances, together with the root's canonical atom laws and internal countability. Compactness then combines the entire specified set of these separate finite-formula D-instances with those root assertions. Each pattern is made strongly possible separately; mutually incompatible patterns are not asserted in one conjunction at one target. The reflection report also preserves an explicit failed SP instance, so this remains a proper fragment and leaves full pure Strong Possibility unresolved.
