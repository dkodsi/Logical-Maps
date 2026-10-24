# Effective positive model theory: low general Gallin models

Research note by OpenAI Codex (GPT-6), 22 October 2026. Ordinary mathematical proofs; no Lean claim, human-check claim, or claim of novelty. No database records are changed. New arguments here should have direct source `misc` if recorded. The note works in ordinary classical set-theoretic metamathematics, with choice for full-model consistency witnesses and the standard Low Basis Theorem.

## 1. Exact theories and recorded evidence

The object language throughout is the map's fixed relational type language: base types e,t and sigma→tau only if tau is not e. Put

- B = C + □Plenitude = C + □ND + Atomicity;
- F = C + □Functional Choice.

These are whole type schemata, with every object variable closed before boxing. C is fixed; no equivalence proved merely from an optional premise is fed into Logical Equivalence, and no optional premise is necessitated.

Read sources: `topics/classicism/AGENTS.md`, `topic.yaml`, `background.md` (Framework, Notation, Conventions), principles `necessary-functional-choice-r`, `necessary-plenitude-r`, `necessary-distinctness-necessary-r`, `atomicity-r`, `infinity-e`, `axiom-of-infinity-e`, `axiom-of-infinity-t`; full-Henkin singleton/infinite model records and `henkin-without-relational-choice`.

A proved-only `load_topic`/`Engine` query, with optional assumptions in the queried premise set and empty engine background, gives:

- F entails □Plenitude by `necessary-functional-choice-r-implies-necessary-plenitude-r`;
- □Plenitude entails □ND by `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`;
- □Plenitude entails Atomicity by `necessary-plenitude-r-implies-atomicity-r`;
- □ND + Atomicity entails □Plenitude by `c5-and-atomicity-imply-necessary-plenitude`.

The engine also returns separation models for B not implying F, including `henkin-without-relational-choice`. Its hypothesis is a model of ZF without choice, used for the internal full type construction; do not silently describe that construction as an externally full hierarchy in an ambient ZFC universe. Its source is Bacon–Dorr, *Classicism*, draft 16 May 2023, §2.3 n.46, p.32. The equivalence B is from §2.3, p.33. None of the effective bounds below asserts that B and F have the same model class.

## 2. Both positive theories are computably enumerable

Admitted types, well-typed finite terms, substitutions, type-schema instances, and the displayed extra axioms of B and F are effective. H has an effective finitary calculus. The H-theoremhood side condition on Logical Equivalence does not obstruct enumeration: enumerate H-proofs and output the associated identity axioms, or require each use of Logical Equivalence in a C-proof certificate to carry its H-proof. Enumerate the finite H-closure derivations from these axioms. This enumerates C and preserves exactly its theoremhood restriction.

Adding either positive schema preserves computable enumerability. So does adding either Infinity schema, either Frege Axiom of Infinity, their boxes, or any further c.e. set of well-typed optional axioms. This is about syntactic consequence, not validity in full models. Recursive enumerability does not mean decidability; §8 gives a sharp lower bound.

## 3. An explicit recursive first-order presentation of auxiliary Henkin models

Use an *auxiliary semantic language*, not an enlargement of the original theory. It has base types e (individuals), s (worlds), and o (two ordinary truth values). Generate arrow types alpha→beta whenever beta is neither e nor s. Thus every arrow ends in o; the required types below are all available without e→e or s→s operations.

Use a countable many-sorted first-order language with a sort D_alpha for each auxiliary type, constants 0,1 in D_o, a distinguished w0 in D_s, and application functions

    app_alpha,beta : D_(alpha→beta) × D_alpha → D_beta.

Its elementary axioms are:

1. Every sort is nonempty; D_o consists of exactly the distinct elements 0,1.
2. Extensionality at each arrow type:

       (∀x app(f,x)=app(g,x)) → f=g.

3. Definable comprehension. For every first-order formula phi(x1,...,xn,ybar), with xi of types alpha_i and arbitrary finite parameter tuple ybar, include

       ∀ybar ∃P^(alpha1→...→alphan→o) ∀x1...xn
          (P[x1,...,xn]=1 ↔ phi(x1,...,xn,ybar)).

   Empty tuples are allowed. The formula may quantify over any auxiliary sorts.

This is a recursive axiom schema in a recursive language. Application plus extensionality permits an induction on types identifying each arrow-sort element with an actual function on the preceding domains. Comprehension supplies all definable relational functions, including the standard Boolean, equality, quantifier, and lambda interpretations. In particular it supplies a lambda with relational output beta by flattening beta to a finite argument list ending in o. Uniqueness follows from iterated extensionality. It follows that every model is an ordinary extensional general/Henkin type structure; fullness is not required.

For F add the following auxiliary choice schema, for all alpha and relational beta (beta not e,s):

    ∀R^(alpha→beta→o)
       [(∀x ∃y Rxy=1) → ∃f^(alpha→beta) ∀x Rx(fx)=1].

Call the resulting c.e. first-order theory H_ch. H_0 denotes the theory without that schema. A full hierarchy over arbitrary nonempty sets D_e,D_s, with D_o={0,1}, satisfies H_0; it satisfies H_ch in ordinary metatheory with choice.

**No hidden second-order semantics.** All quantifiers in the preceding axioms are ordinary sorted first-order quantifiers. Comprehension ranges over syntactically enumerated formulas; it does not quantify over arbitrary external subsets. Requiring every external function instead would destroy the low countable-model argument when base domains are infinite.

## 4. Gallin translation and its verification

Define the recursive object-type translation

    e* = e;  t* = s→o;  (sigma→tau)* = sigma*→tau*.

Let G_sigma = D_(sigma*). An original proposition is therefore an available function from D_s to {0,1}. Original application is auxiliary application; original lambda is auxiliary lambda. Logical terms are interpreted by

    (¬p)(w)       = not(p(w)),
    (p ∧ q)(w)    = p(w) and q(w),
    (∀_sigma P)(w) = 1 iff ∀a∈G_sigma P(a)(w)=1,
    (= _sigma)(a,b)(w) = 1 iff a=b.

Each displayed function exists by auxiliary comprehension. At the distinguished world w0, truth means p(w0)=1; any other world gives another evaluation of the same structure.

### 4.1 Soundness for the fixed C

The standard induction on H-derivations is valid at every w: Boolean rules use ordinary truth, quantifier rules range over the fixed nonempty G_sigma, equality is literal identity, and beta/eta conversion holds for actual extensional functions. If H proves formulas A and B equivalent, their denotations agree at every world and every assignment. Extensionality then identifies the denotations of their lambda abstracts. Thus Logical Equivalence is sound with exactly the H-theoremhood condition required by C. H-closure remains sound. Every translated structure above is consequently a C-model.

Original Box p is p=top. Since equality is literal equality between functions, this holds at a world iff p(v)=1 for *every* v∈D_s. Box is therefore universal S5 necessity, with no use of an optional necessitation rule.

### 4.2 C5 and Atomicity already hold over H_0

Every original equality and disequality is constant across worlds. Hence every instance of □ND holds.

For relational tau=sigma1→...→sigman→t, every f∈G_tau has a support

    S_f = {(a1,...,an,w): f[a1,...,an](w)=1}.

Iterated auxiliary extensionality gives f=g iff S_f=S_g. Pointwise Boolean operations give original algebraic order f≤g iff S_f⊆S_g. If f is not bottom, choose a point (abar,w)∈S_f. The characteristic function

    delta_(abar,w)(xbar)(v) = 1 iff (xbar=abar and v=w)

belongs to G_tau by comprehension. Its support is exactly that singleton, so it is an atom below f. This includes n=0, the propositional type. Atomicity holds at every world. Consequently the resulting model satisfies B (indeed boxed Atomicity), by the recorded equivalence.

This proof does *not* conclude that every external set of support points is represented. It uses only singletons, which the general Henkin domains contain by comprehension.

### 4.3 Necessary Functional Choice over H_ch

Fix a world w and an original U of type sigma→tau→t, tau≠e, such that

    ∀x∈G_sigma ∃y∈G_tau U(x)(y)(w)=1.

Auxiliary comprehension supplies the ordinary binary predicate R(x,y) iff U(x)(y)(w)=1. Since tau* is an auxiliary relational type, the corresponding auxiliary choice instance supplies f∈D_(sigma*→tau*) with R(x,f(x)) for every x. This f belongs exactly to the required original operation domain G_(sigma→tau). Thus original Functional Choice holds at w. Since w was arbitrary, its closed instance has proposition value top, proving □Functional Choice. The argument works at every original pair of types.

Choice is an additional axiom of H_ch; it is not silently inferred from Henkin comprehension. General Henkin models of H_0 need not satisfy it.

### 4.4 Direct unique choice, if desired

H_0 suffices for original □Plenitude without invoking the recorded equivalence. At a fixed w let U(x,y,w) determine exactly one original relational y for each x. Flatten tau* to beta1→...→betak→o. Define by comprehension

    f(x)(zbar)=1 iff ∃y [U(x)(y)(w)=1 and y[zbar]=1].

For each x, uniqueness supplies its unique y, and the displayed f(x) agrees with y on every zbar. Extensionality gives f(x)=y. Hence f is the required selector. Arbitrary serial relations do not admit this argument, because the union of several possible y's need not itself be one of the permitted y's.

## 5. Consistency witnesses with genuine worlds and Infinity

These are consistency witnesses for the c.e. auxiliary theories to which the low-model lemma will be applied.

### 5.1 Finite nontrivial worlds

Add constants w0,w1 with w0≠w1 and ∀w(w=w0∨w=w1). Full auxiliary domains over D_s={0,1}, D_e=N satisfy H_ch. The corresponding original propositions are the four subsets of two worlds. They distinguish the worlds, and the Fregean Axiom fails at either world: top and the singleton containing that world are both true there but are distinct propositions.

Add the translated original Frege Axiom of Infinity at e, optionally boxed. It holds in this full witness. Explanation: at each sigma, full domains contain the characteristic predicate of the external set of all iterates Suc_sigma^n(0_sigma), so the impredicative FiniteCardinality predicate picks out exactly those iterates. At e each such numeral is the cardinality predicate for n-element local extensions. The universal e-property is infinite at every world and has none of those finite cardinalities. The same argument establishes every Infinity_e schema instance. It does not establish Infinity_t here, because G_t has four elements.

### 5.2 Infinitely many worlds and individuals

Take full auxiliary domains over D_s=N and D_e=N. Then G_t=P(N). Original Functional Choice holds necessarily by §4.3. Both original Frege Axioms of Infinity, at e and t, hold at every world: each of G_e and G_t is infinite, and the full-domain characterization of finite cardinalities in §5.1 applies to each.

Consequently H_ch plus the translations of □AxiomOfInfinity_e and □AxiomOfInfinity_t is consistent. One may additionally add the recursive external cardinality schemata making D_s and D_e infinite. These latter schemata concern auxiliary sort sizes, not the original Frege predicates. The full witness satisfies them simultaneously.

Keeping the translated Frege axioms explicit is deliberate. Infinitely many elements of a sort, expressed by all fixed finite lower bounds, must not be substituted for its Frege Axiom of Infinity in an arbitrary Henkin model.

## 6. Low complete Henkin models: detailed effective lemma

**Lemma.** Every consistent c.e. theory T in a recursive countable many-sorted first-order language has a countable model whose complete elementary diagram, in a suitable effective presentation, has low Turing degree.

Here low means that the Turing jump of the diagram has degree 0′, the degree of the ordinary halting problem. This is an existence theorem, not a uniform algorithm choosing a model without an oracle.

**Proof.** Add a recursively generated supply of fresh witness constants in stages. For every existential formula in each stage's language add a later-stage fresh constant and its Henkin witness axiom. Also give every sort a constant. The expanded theory T^H is c.e. and consistent: every finite collection of fresh witness axioms is consistent by the ordinary witness-extension argument, and first-order compactness gives consistency of their union.

Effectively enumerate the sentences psi_0,psi_1,... of the expanded language. A binary path D chooses each psi_i or its negation. Impose the requirements that the chosen set together with T^H has no finite proof of contradiction. These form a nonempty effectively closed subset of Cantor space: a finite inconsistent initial choice is effectively recognizable by eventually finding a proof of contradiction, while consistency of T^H guarantees a complete consistent extension. Equivalently use the computable binary tree which at length n checks all contradiction proofs of code at most n using the first n enumeration stages of T^H and the first n decisions. Any finite obstruction is eventually rejected.

By the Jockusch–Soare Low Basis Theorem this nonempty effectively closed class has a low member D. D determines a complete consistent Henkin theory extending T^H. Form its usual sorted term model: identify same-sort closed terms u,v precisely when (u=v)∈D. Because D decides equality, choose the least numbered term in each equivalence class. Membership in this set of representatives is D-decidable (check finitely many smaller terms), and functions are D-computable by forming their term and choosing its least representative. The complete elementary diagram is D-computable by the Henkin truth lemma: for a formula with named representatives, test its closed instance in D. Therefore this diagram is low, since it is Turing reducible to a low set. QED.

This proof uses only the Low Basis Theorem as its computability-theoretic input. For an accessible primary-author exposition see Andrew E.M. Lewis-Pye, *The search for natural definability in the Turing degrees*, Computability 1 (2012), §8.1, Theorem 8.2, p.22, and the immediately following completion corollary: https://lewis-pye.com/wp-content/uploads/2018/08/nd_cie.pdf . The original theorem is Jockusch and Soare, *Π^0_1 classes and degrees of theories*, Transactions AMS 173 (1972), pp.33–56, DOI https://doi.org/10.1090/S0002-9947-1972-0316227-0 . The original PDF was not directly retrievable in this run; the theorem statement and completion application were checked in Lewis-Pye's author-hosted paper.

## 7. Main upper bounds and their exact scope

Apply §6 to the auxiliary theory H_ch and the relevant added axioms of §5.

**Theorem.** Each of the following has a countable general Gallin model with a low complete elementary diagram:

1. F, with any prescribed positive finite number of worlds;
2. F + □AxiomOfInfinity_e, with exactly two worlds;
3. F + □AxiomOfInfinity_e + □AxiomOfInfinity_t, with infinitely many worlds and individuals.

Every one is also a model of B. In item 2 the model is nonextensional, with exactly four original propositions. In item 3 every auxiliary and original sort is countable, worlds and individuals are infinite, and propositions are infinite but do not exhaust the external powerset of the worlds.

**Why the bound transfers to the original typed semantics.** The type and formula translations in §4 are recursive. A complete elementary diagram computes the unique representatives of definable logical operations and abstractions: search the countable target sort and test the first-order defining formula, which has a unique solution by comprehension and extensionality. It therefore computes original term denotations, equality, application, the logical constants, and truth at the named w0. It also computes satisfaction of original formulas with parameters by translation. Thus the result supplies the stronger semantic presentation needed for a complexity comparison, not just an unspecified low relational reduct.

Every low degree is strictly below 0′: it is at most its jump, and if it computed 0′ its jump would compute 0″, contradicting lowness. Hence these models' presentations do not compute 0′. The theorem makes no claim that the presentations with Infinity are computable.

**Uniformity qualification.** For any specified consistent c.e. auxiliary extension, its Henkin completions form a nonempty Π^0_1 class. Low Basis supplies a low path, but not a computable uniform choice of such a path. The semantic-model existence problem retains the usual nonconstructivity of choosing complete theories.

**Full-model qualification.** With infinitely many worlds, any full Gallin model has G_t=P(W), which is uncountable. With infinitely many individuals and at least one world, a full model already has an uncountable type et. These full structures cannot have a countable presentation by natural numbers. The low countable models are deliberately general/Henkin models. The full witnesses establish consistency, after which first-order compactness/Henkinization yields different, nonfull models.

## 8. Theoremhood remains Σ^0_1-complete, even with Infinity

The following strengthens the warning that a low model is not an algorithm for theorems of the incomplete theory.

**Proposition.** For each of B and F, with or without either/both Frege Infinity axioms or their boxes, the set of theorems is c.e.-complete under many-one reductions. The set of provable closed pure identities is likewise c.e.-complete.

**Proof.** The upper bound is §2. Reduce ordinary first-order relational validity, whose degree is c.e.-complete. Given a first-order sentence phi in a finite relational vocabulary Rbar, introduce a unary predicate P and relativize all its individual quantifiers to P. Form the closed pure higher-order sentence

    A_phi = ∀P^(et) ∀Rbar [(∃x Px) → phi^P].

All relation symbols become variables of admitted relational types. When phi is first-order valid, the standard effective relativization argument gives an H-proof of A_phi, and hence a C-proof. Theorem necessitation gives C⊢A_phi=top; no optional hypothesis has been necessitated.

When phi is invalid, it has a nonempty countable countermodel by the first-order downward Löwenheim–Skolem theorem (finite countermodels are included). Embed its domain as a nonempty subset P of N. In the full Gallin model over G_e=N and W=N, interpret P and Rbar by rigid predicates giving that counterstructure on P. This model satisfies F and both boxed Frege Infinity axioms, by §5.2, while A_phi is false at every world. Hence neither A_phi nor A_phi=top is provable in any of the stated positive theories. This is the required effective reduction. QED.

The quantifier relativization matters: merely universally closing Rbar in phi would not preserve arbitrary finite countermodels after an Infinity_e assumption is added. The new unary P lets the full infinite positive model contain the desired finite or countable counterstructure.

Church's undecidability alone gives undecidability, but the sharpened conclusion uses the standard many-one c.e.-completeness of first-order relational validity. If an integration note chooses not to import that stronger standard theorem, state only undecidability; none of §§3–7 depends on c.e.-completeness.

## 9. Comparison to the maximalist obstruction, with presentation discipline

The base non-r.e. claim is already explicit in Bacon–Dorr, accessible draft of 1 July 2022, §2.4, p.35 n.52 (a different draft from the map's normal 16 May 2023 source). The companion root note `maximalism-modal.md` §9 establishes the stronger statement that a consistent c.e. extension of C cannot entail pure Max(C). Its mechanism is that Max(C) fixes the truth of every closed pure identity A=B to exactly C-theoremhood of that identity. Once C's identity theorem set is shown c.e.-complete, every adequate Max(C) presentation computes 0′ by evaluating those identities.

The upper bound proved here yields a precise contrast: F, and therefore B, has low countable general Gallin presentations even with both boxed Frege Infinity axioms; an adequate Max(C) presentation cannot be low. This compares the existence of presentations and their computational information. It does not say all positive models are low, or that full positive structures are countable, or that positive theoremhood is decidable.

An *adequate presentation* must compute denotations of the original finite typed terms and their equality (in particular closed pure identities). A full operational diagram with application, logical constants, and effective lambda interpretation suffices. An arbitrary atomic diagram of a reduct which forgets lambda interpretation and represented quantifier operations need not suffice without an additional argument. The upper bound here has no such weakness: the complete auxiliary elementary diagram computes all required original operations and truth.

For exactly two finite worlds and a finite individual base, the entirely full hierarchy is actually computable by finite truth tables: each individual sort is finite, its cardinality is computable recursively from its type, all functions are finite tables, and every term can be evaluated effectively. This gives computable nonextensional positive models *without* Infinity_e. That special argument must not be extrapolated to infinite full domains.

## 10. What is and is not settled

Proved here: effective positive axiom schemes; recursive many-sorted Gallin coding; low countable general Gallin models of the stronger positive package, including nonextensional and both-Infinity versions; positive theoremhood lower bounds. The same low existence argument applies to any further c.e. auxiliary strengthening for which consistency is separately established.

Not claimed: a completeness/representation theorem saying *every* B-model or F-model arises from precisely the auxiliary coding used here; a uniform computable model selector; a computable model with either Frege Infinity axiom (indeed §13 rules out adequate computable presentations); a cardinality bound for full models; any absolute strict ranking between B and F by Turing degree; or an inconsistency result for Max(C). The general Gallin subclass suffices for the stated existence contrast.

## 11. Low infinite Gallin models necessarily have nonstandard Frege numbers

This section concerns the general Gallin models constructed from the auxiliary H_0/H_ch structures of §3. It does not claim that arbitrary C-models have literal constant domains or that maximalist models lack standard arithmetic points.

Fix an original counting type sigma whose domain G_sigma is externally infinite, and let nu=(sigma→t)→t, N=FiniteCardinality_sigma, with the map's zero, successor, Sum, and Prod. Write nbar for the value of Suc^n(0), for each ordinary n∈N.

### 11.1 Standard numeral facts need no external fullness

For every standard n and every original property X∈G_(sigma→t), induction on n using the definitions proves, at any world w,

    nbar(X)(w)=1 iff {a∈G_sigma : X(a)(w)=1} has exactly n elements.

The zero step is the universal emptiness definition. The successor step is ordinary deletion of a chosen element, and equality of sigma-objects is literal equality in the Gallin structure. Since G_sigma is infinite and comprehension supplies every finite rigid subset, all nbar are pairwise distinct as nu-objects. Each is in N at every world by the finite external induction applying the defining inductiveness condition for N.

### 11.2 The natural-number domain is world-independent in this subclass

For every available original property R∈G_(nu→t) and each w∈D_s, auxiliary comprehension supplies

    R^w(a)(v)=R(a)(w)

for every a,v. This is an original property in the same domain, now with a constant world profile. Accordingly the collection of subsets of G_nu appearing as slices {a:R(a)(w)=1} is the same for every w: each slice at one world is the slice of R^w at every world. The zero object and successor operation are the same global objects at all worlds. Intersecting the available slices which contain zero and are successor-closed therefore yields the same subset N^G of G_nu at every world. The same slice argument applies to the available binary relations used in Sum and Prod. In particular these arithmetical relations are also world-independent.

This is an argument about the present auxiliary-Henkin Gallin subclass. A representation theorem is needed before transferring it indiscriminately to every model in some broader semantics.

### 11.3 If N contained only numerals, its arithmetic would be standard

Assume N^G={nbar:n is an ordinary natural number}. The numeral map is a bijection by §11.1 and the assumption. We verify that the map's impredicative Sum and Prod induce the usual addition and multiplication. The argument requires only definable relations, not arbitrary external subsets.

For standard a,b, every relation R witnessing the premises in the definition of Sum(abar,bbar,cbar) contains (0,abar) and is closed under simultaneous successor on N. A finite induction of length b therefore gives R(bbar,(a+b)bar), proving Sum(abar,bbar,(a+b)bar).

For the converse use the available, equality-defined relation

    R(i,j) iff j=Suc^a(i).

It contains (0,abar) and is closed under simultaneous successor. Thus Sum(abar,bbar,cbar) entails cbar=Suc^a(bbar)=(a+b)bar. Pairwise distinction of numerals gives c=a+b.

For products, a finite induction of length b through the defining relation and the just-verified addition establishes Prod(abar,bbar,(ab)bar).

To exclude an incorrect product c≠ab, use the following finite, hence definable relation (with a,b fixed standard integers):

    R(i,j) iff AND_{k=0}^b (i=kbar → j=(ak)bar).

It contains (0,0). We check its required closure under the rule R(i,j) and Sum(abar,j,k) imply R(Suc i,k), for i,j,k∈N. By the standardness assumption let i=lbar. If l+1>b, the successor's antecedents in the finite conjunction are all false, so there is no restriction. If l+1≤b, then R(i,j) forces j=(al)bar; verified addition forces k=(a+al)bar=(a(l+1))bar, precisely the next requirement. The case Suc i=0 does not occur because distinct numerals have the usual successor chain. Thus R has the required closure, but R(bbar,cbar) fails for c≠ab. This refutes an incorrect Prod instance.

The first-order structure with domain N^G and these zero, successor, Sum, Prod relations is therefore exactly standard arithmetic. Induction on ordinary arithmetical formulas gives a recursive truth-preserving translation into original typed formulas, restricting numerical quantifiers to N at the evaluation world.

### 11.4 The nonstandardness theorem

**Theorem.** If G_sigma is externally infinite and an adequate presentation computes satisfaction of the original formulas at a world w, then standardness of N_sigma at w would make that presentation compute true first-order arithmetic. In particular it would compute 0′. Consequently, in every low complete-diagram Gallin model from §7 with G_sigma infinite, N_sigma contains a nonnumeral; indeed it does so at every world.

**Proof.** Given an ordinary arithmetic sentence theta, effectively form its typed translation theta^#. By §11.3, under the standardness assumption theta is true in ordinary arithmetic iff theta^# is true at w. The assumed presentation decides the latter. Standard effective arithmetization of finite computations reduces the halting problem to the true existential sentences of ordinary arithmetic, so 0′ is computable from the presentation. A low presentation cannot compute 0′. World-independence from §11.2 gives the final assertion. QED.

The proof in fact only needs infinitely many sigma-objects externally; for sigma=e this follows already from the Infinity_e schema. It does not require substituting that schema for the stronger Frege Axiom in any internal derivation.

Thus the low two-world models with infinite individuals have nonstandard N_e, and the low infinite-world models in §7 have nonstandard N_e and N_t. The full consistency witnesses over N have standard Frege numbers, but their semantic domains are uncountable and their complete semantic diagrams are not low. This is exactly where the move from full to general semantics changes the arithmetic content.

**Limitation concerning Max(C).** This theorem is not an obstruction to a maximalist model having a standard arithmetic root or some standard arithmetic point. The maximalist presentation lower bound is already at least 0′, so computing standard arithmetic does not contradict that bound. Nor does maximalist availability of arithmetically different possible points imply that every possible point has nonstandard arithmetic. Those are separate claims requiring separate arguments.

## 12. Finite positive conditions and a nonextensional interior for Choice

This section was sent to the parent as a check on a separate topological comparison. The parent owns the Stone-space application.

A proved-only Engine query gives the exact finite reduction

    B = C + [□ND_t ∧ Atomicity_t].

The forward implication is type restriction. For the reverse, `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` gives C5; `necessary-nd-implies-bf` gives BF; `atomicity-t-and-bf-imply-atomicity` lifts Atomicity_t to every relational type; and the recorded C5+Atomicity equivalence gives B. In particular B is finitely axiomatizable *over C*, despite its displayed all-type schema. Adding either or both original Frege Infinity axioms (optionally boxed) is still a finite extension over C and has the full witness of §5.2.

There is also a finite, nonextensional sufficient condition for the whole F schema. Fix positive ordinary integers n,m and put

    V_n,m := □ND_t ∧ □AtMost_n(e) ∧ □AtMost_m(t),

where AtMost_n(sigma) is the ordinary finite first-order sentence saying there are at most n sigma-objects. Over C this single finite pure condition entails every □Functional Choice instance.

Proof: the first conjunct gives C5, hence BF and ordinary functionality. At any evaluation world, the two boxed bounds make the base domains finite. Functionality makes an operation determined by its application table; induction on a fixed type gives |G_(sigma→tau)|≤|G_tau|^|G_sigma| and hence finiteness at every fixed type. (As an internal proof, enumerate the two finite domains and use the pigeonhole principle on the finitely many possible tables.)

For a serial U of type sigma→tau→t, enumerate its finite input domain by a1,...,ak, choose yi with U(ai,yi) for each i, and take distinct ai. This uses only finitely many existential eliminations. Form the admitted relational-output term

    f(x) = OR_{i=1}^k [ (x=ai) AND_tau yi ].

Here propositional multiplication is lifted pointwise through tau. Under C5 every true equality mask is top, by NI, and every false one is bottom, by ND. Thus f(ai)=yi as objects, using Boolean identities at tau. It follows that U(x,f(x)) for every x. The argument applies at every world because the bounds and C5 hold there, giving the boxed FC instance. No arbitrary external set of functions is assumed.

For n=1,m=4 the full two-world Gallin model with singleton individuals satisfies V_n,m and refutes the Fregean Axiom. Consequently the finite condition V_1,4 ∧ ¬Fregean is consistent and forces the entire F theory while preserving genuine contingent propositions. This supplies a nonempty finite-condition region of the F locus; it makes no claim of such an interior with Infinity_e, which is a separate issue.

## 13. Exact oracle threshold with a Frege Axiom of Infinity: PA degrees

This strengthens the earlier cautious upper bound. It uses two identified standard results, rather than claiming the Low Basis argument alone excludes computability.

A Turing degree d is a **PA degree** if it computes a complete consistent extension of first-order Peano arithmetic. The standard basis characterization says that d is PA iff every nonempty effectively closed subset of Cantor space has a member computable in d. This is Theorem 8.4 (attributed there to Solovay, extending Scott's basis theorem) in Lewis-Pye's author-hosted paper cited in §6, p.23. Only this characterization is imported here; the reductions below are new applications to the present theories.

For the arithmetic interpretation, Goodsell, *Arithmetic is Necessary*, draft 5 June 2024, §4, Lemma 1, p.12, states that HK proves I→A for every theorem A of Peano arithmetic, with quantifiers restricted to N and addition/multiplication expressed relationally by Sum/Prod. C extends HK. The local `countable-boolean-completeness-implies-necessity-of-arithmetic.md`, Lemma 7, explicitly invokes that result. The exact statement and p.12 locator were also confirmed in the author-deposited source indexed at https://philarchive.org/archive/GOOAIN ; direct PDF opening returned 403, but source-targeted retrieval returned Lemma 1 and its definitions. It is a source theorem, not a new PA proof attributed to this note.

### 13.1 Frege Infinity supplies the arithmetic premise

In fact C plus the Frege Axiom of Infinity at sigma proves I*_sigma, and hence I_sigma. Here is the argument, spelling out its dependencies.

For a finite cardinality n, its application is invariant under current coextension of properties. Prove this by the impredicative induction defining N: zero is emptiness; for a successor, delete the same chosen witness from the two coextensive properties and apply the induction hypothesis. This uses no identity between merely coextensive properties.

The Infinity axiom then gives realization of every finite cardinality. Apply the defining induction to W(n):=Nn∧∃X nX. Zero is realized by the empty property. Given nX, X cannot be universal, since coextension invariance would contradict Infinity. Choose a outside X. The property X∪{a} realizes Suc n, because deleting a returns a property coextensive with X. Thus every N-number has an instance.

Zero-not-successor is immediate from the definitions. To prove injectivity, let Nm,Nn and Suc m=Suc n. Realize that common successor at X. Unfolding produces a,b∈X with m(X−a) and n(X−b). If a=b, m,n share an instance; if a≠b, the recorded finite-cardinality Swap lemma gives n(X−a), again a common instance. The recorded Exclusivity lemma makes m=n. These two recorded lemmas are proved in `topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md` §1, Lemmas 3–4. Consequently I*_sigma holds; T gives I*_sigma→◇I*_sigma=I_sigma.

This proof is also the mechanism developed in the companion research note `frege-infinity-20261022-1726.md` §§1,7. It has been reproduced here so that the effective conclusion does not depend on an unexplained new arrow.

### 13.2 Lower bound: every adequate model computes a PA completion

Let M be any model of C plus the Frege Infinity axiom at sigma, with a presentation computing truth of its closed original formulas. By §13.1 and Goodsell's Lemma 1, its interpreted arithmetical theory

    A_M = {theta : M satisfies the standard typed translation theta^#}

contains PA. Because it is the theory of a classical structure, it is complete and consistent. Translation is recursive, so A_M is computable from the presentation. Its degree, and every oracle computing that presentation, is therefore PA.

An equality-only version is available for B-models: B gives No Pure Contingency, so a closed pure arithmetical translation theta^# is true iff theta^#=top is true. Thus in B+FregeInfinity the closed-pure identity diagram alone already computes a PA completion. This last observation should use the recorded proved No Pure Contingency result, not presume it in bare C.

### 13.3 Matching upper bound

Let d be PA. The completions of the consistent c.e. Henkin theory constructed in §§3–6 form a nonempty effectively closed class. The PA-degree basis characterization supplies a complete Henkin theory D computable in d. The term model and the whole original Gallin semantic presentation are computable in D, hence in d.

Choose the strongest auxiliary theory in §5.2, which gives F together with both boxed Frege Infinity axioms and infinitely many worlds and individuals. Its model also satisfies every weaker positive package considered here. Alternatively choose the exact two-world theory when that cardinality condition is desired.

**Exact theorem.** For each T among

- C + one Frege Infinity axiom at e or t;
- B + one Frege Infinity axiom at e or t;
- F + one Frege Infinity axiom at e or t;
- any of those packages additionally requiring both Frege Infinity axioms, boxed or unboxed;

an oracle degree d computes some countable adequate general model of T **iff d is a PA degree**. For the positive packages, the witnessing model can be chosen in the general Gallin subclass. The two-world version remains available when only e-Infinity is required. The necessity direction applies to any adequate semantic presentation, not merely the auxiliary subclass.

The displayed statement is about *an oracle's ability to compute some presentation*, i.e. a degree upper bound. It does not assert that the set of exact least degrees of individual isomorphism types is the PA degrees, or that each theory has a model whose least presentation degree is any prescribed PA degree. Those are stronger degree-spectrum questions.

### 13.4 Consequences and boundaries

No computable adequate presentation exists with a Frege Infinity axiom: a computable complete consistent PA extension would contradict the ordinary incompleteness theorem. Low noncomputable PA degrees do exist by Low Basis, and §§6–7 realize the corresponding positive models. Thus the useful sharp description is **PA-level oracle choice, allowing low degrees**, not computability.

The arithmetic-interpretation proof alone does not establish the same lower bound from the Infinity schema: that schema need not give the internal successor injectivity needed by Goodsell's interpretation. However, the independent finite-computation argument in §16 establishes exactly the same PA lower bound from the weaker schema. Section 11's nonstandardness argument for low models with infinite domains remains valid separately.

Nor is this a strict computability distinction between B and F: after a strong Infinity axiom, they have exactly the same oracle threshold for obtaining *some* countable model. Their structural differences and their differing model classes remain substantial. The contrast with Max(C) is that pure maximalist presentations encode the fixed 0′-complete identity theory of C, whereas positive models can be obtained in PA degrees strictly below 0′.

## 14. Completeness persists under every consistent effective strengthening with Infinity

The following is stronger than §8 because no standard-arithmetic model of the additional axioms is assumed. The proof is the unrelativized form of the direct recursion argument in the companion `max-degree.md` §10.4.

**Theorem.** If T is any consistent c.e. theory whose consequences contain C plus one Frege Axiom of Infinity, then its set of closed pure theorems is Σ^0_1-complete under ordinary computable many-one reductions. This applies in particular to every consistent c.e. strengthening of either positive package with a Frege Infinity axiom.

Proof. By §13.1 and Goodsell's arithmetic interpretation, T proves every translated PA theorem. Fix pure arithmetic formulas H_b(n), b=0,1, saying that ordinary machine n on input n halts with output bit b, using the map's N, Sum and Prod. Put

    V_b = {n:T⊢H_b(nbar)}.

These are disjoint c.e. sets: arithmetic proves determinism, and T is consistent. They contain the respective ordinary diagonal halting sets K_b={n:phi_n(n) halts with output b}, because actual finite computations have PA-verifiable codes.

The parameterized recursion theorem yields a computable p(n) such that program p(n), ignoring its input, dovetails:

1. If program n on n halts, return 0.
2. If p(n) is enumerated into V_0, return 1.

Return whichever is found first, with a fixed tie rule. The enumerator for V_0 is a fixed effective parameter of this construction.

If n does not halt but p(n) belongs to V_0, only the second search succeeds. Thus program p(n) outputs 1, putting p(n) in K_1⊆V_1, a contradiction. Hence n∉K implies p(n)∉V_0.

If n halts but p(n) does not belong to V_0, only the first search succeeds. Thus program p(n) outputs 0, putting p(n) in K_0⊆V_0, a contradiction. Hence n∈K implies p(n)∈V_0.

Therefore n∈K iff T⊢H_0(p(n)bar), a computable many-one reduction into the pure T-theorems. The c.e. upper bound is immediate. QED.

This is a consistency argument, not a Σ_1-soundness argument. T may assert nonstandard apparent halting computations; disjointness and correctness of genuinely finite computations suffice. Nor does an arbitrary optional hypothesis get necessitated: the target formulas H_b are unboxed translated arithmetic sentences.

Section 16 extends this robustness from a strong Frege Infinity axiom to the weaker Infinity schema. With no Infinity assumption at all, robustness fails: a positive theory has a computable finite-domain model, whose decidable complete theory is a consistent c.e. strengthening. Thus the displayed lower bound for *every* strengthening is not a consequence merely of B or F having Σ^0_1-complete theoremhood.

## 15. Uniform comparison as a Medvedev degree

This section turns the oracle-capacity comparison into an actual uniform mass-problem comparison. All languages, formula enumerations, witness-constant schedules, and proof enumerations are fixed once the displayed theory is fixed. No claim about preserving an input completion's exact theory when constructing a model is made.

### 15.1 Coding the solution sets

For a consistent theory T, let Comp(T) be the set of characteristic functions of complete consistent deductively closed extensions of T in its original pure language. Let Model(T) be the set of countable BBK/general-model codes with numbered sorted domains, equality, uniform interpretation of original finite typed terms, and truth valuation. These are the adequate codes used in the effective comparisons. A model code uniformly computes its complete actual pure theory by evaluation.

Let PAcomp be the usual mass problem of complete consistent first-order PA extensions. For the relativized version, PAcomp(0′) consists of complete consistent extensions of arithmetic in a language with a unary predicate O, containing PA, induction for every formula of the expanded language, and each correct literal O(nbar) or ¬O(nbar) for the standard halting set. Equivalently one may use binary DNR functions relative to 0′; the uniform conversions are described below. This definition explicitly includes the oracle information and expanded induction.

A mass problem A is Medvedev reducible to B when one fixed computable Turing functional converts every solution of B into a solution of A. Our statements concern this uniform reducibility, not merely the existence of a Turing reduction separately for each input.

### 15.2 The positive complete-theory problem is uniformly equivalent to PA completion

Fix T to be B or F with at least one Frege Infinity axiom, and optionally either or both boxes/additional Infinity axioms as in §13. Then

    Comp(T) ≡_M Model(T) ≡_M PAcomp.                 (15.1)

**From Comp(T) to PAcomp.** Given Γ∈Comp(T), define A_Γ by theta∈A_Γ iff theta^#∈Γ, using the fixed arithmetic translation. Section 13 proves that A_Γ is a complete consistent extension of PA. Membership is a single Γ-query after computably translating the input formula, so the transformation is uniform. The same map composed with model evaluation works from Model(T).

**From PAcomp to a model.** Given A∈PAcomp, define

    d(e)=1 if H_0(ebar)∈A, and d(e)=0 otherwise,

where H_0 is the ordinary arithmetic formula for diagonal halting with output 0. If machine e actually outputs 0, PA proves H_0(ebar), forcing d(e)=1. If it actually outputs 1, PA proves H_1(ebar), and determinism forces ¬H_0(ebar) in A, so d(e)=0. Thus d is binary DNR. This transformation is uniform, using only queries to A.

Choose the fixed consistent c.e. auxiliary Henkin theory U_H from §§3–6 whose general Gallin models satisfy the strongest specified T. Enumerate its sentences phi_0,phi_1,... . Having chosen a finite consistent decision set Δ, compile a program e(Δ,phi_s) which ignores its input and searches U_H+Δ proofs, returning 0 upon finding a proof of phi_s and returning 1 upon finding a proof of ¬phi_s. If d(e)=1, choose phi_s; otherwise choose ¬phi_s. If either side was already forced, DNR forces the corresponding consistent choice. If neither side was forced, either choice is consistent by the deduction theorem. This is a uniform d-computable complete Henkin construction.

The representative term model is computed uniformly from those decisions, exactly as in §6. Its Gallin interpretation gives a Model(T) code uniformly. Evaluation then gives a Comp(T) code. This proves all reductions in (15.1).

The reduction from an arbitrary Γ∈Comp(T) to a model is allowed to extract its PA completion and build some model of T. It need not return a model realizing Γ. The mass problem asks for *some* solution of T, and preserving Γ would be a different problem with a potentially higher computational cost.

### 15.3 Maximalism is the relativized task

Using the fully audited arithmetic-oracle argument in `max-degree.md` §§8–9 gives

    Comp(Max_C) ≡_M Model(Max_C) ≡_M PAcomp(0′).     (15.2)

Here is the uniformity bookkeeping. In any Γ∈Comp(Max_C), the fixed pure predicate

    J(n)=□(I→Halt(n))

has exactly the correct 0′ answers on standard numerals. Moreover I holds, ordinary arithmetic is interpreted, and the defining N-induction supplies induction for arbitrary expanded formulas using J. Given an arithmetic sentence theta in the language with predicate O, replace O by J and translate arithmetic; querying Γ decides the result. This uniformly returns a complete extension of PA with the correct 0′ diagram and all expanded induction.

Conversely, any such PAcomp(0′) solution uniformly computes a binary DNR^0′ function by the output-0 construction above, now using oracle-computation formulas. A binary DNR^0′ function d itself computes 0′: let e(k) be the index of the oracle program which ignores its input and returns the oracle's kth bit; then 0′(k)=1−d(e(k)). Using this recovered 0′, the proof-search completion algorithm works for the fixed 0′-c.e. Henkinized Max_C theory, and returns a BBK model uniformly. The program indices used in the DNR decisions are compiled without querying 0′; the resulting programs are allowed to query their oracle while running. These are genuine computable Turing functionals on the input solution code.

The same equivalence holds for Max_C plus any *fixed* 0′-c.e. additional theory S consistent with it, using its fixed oracle-enumeration index in the model construction. A varying, unprovided index for S is not silently assumed.

### 15.4 Strictness

Restriction to the ordinary arithmetic language uniformly maps a solution of PAcomp(0′) to a solution of PAcomp. Hence PAcomp≤_M PAcomp(0′).

The converse reduction is impossible. Low Basis gives a low A∈PAcomp. Any value of a computable functional on A is Turing reducible to A and so cannot compute 0′. But every solution of PAcomp(0′) decides the correct O(nbar) literals and therefore computes 0′. Thus

    PAcomp <_M PAcomp(0′).

Combining (15.1)–(15.2) gives a strict uniform computational separation between obtaining a complete positive theory/model with strong Infinity and obtaining a complete pure maximalist theory/model. This comparison is meaningful even though both classes have countable general models and even though the positive theories themselves have undecidable, Σ^0_1-complete theoremhood.

Without any Infinity requirement, both B and F have a computable complete theory and a computable adequate model: take the finite full Gallin structure with one individual and, if nonextensionality is desired, two worlds. Therefore their unrestricted Comp and Model mass problems have the computable Medvedev degree. Adding even the weak Infinity schema raises the positive problem to PA completion, as §16 proves, while Max_C is already at the relativized PA-completion level without an extra Infinity axiom.

**Scope.** These are uniform solvability classifications for the specified complete-theory and adequately encoded model tasks. They do not classify arbitrary bare category/action codes, full uncountable structures, models with prescribed standard arithmetic, or model construction preserving a supplied complete theory.

## 16. The weaker Infinity schema already has the PA oracle threshold

This section strengthens §§13–15. The strong Frege axiom was sufficient for the arithmetic interpretation used there, but it is **not necessary for the computational lower bound**. The lower bound follows from finite computation certificates and finite simulation, even when the internal Frege successor has overflow. This is a new argument in the present notes, not a theorem attributed to the map or to the sources above.

Fix any admitted type sigma. Let InfSchema_sigma contain, for each positive standard integer m, the sentence asserting m pairwise distinct sigma-objects. Only the two recorded instances sigma=e,t are needed for the stated positive comparison.

### 16.1 Effective finite-register-machine convention

Fix an effective enumeration phi_e of partial computable functions. Effectively compile e into a deterministic, zero-input register program P_e such that:

- if phi_e(e) halts with output 0, P_e eventually enters its designated state h0;
- if phi_e(e) halts with output 1, P_e eventually enters its designated state h1;
- all other behavior may diverge.

Use the standard instruction set INC(j,q), which increments register j and goes to q, and DECJZ(j,q_zero,q_pos), which goes to q_zero without changing registers if register j is zero and otherwise decrements j and goes to q_pos. Registers initially contain zero. Each program has finitely many registers and finitely many states; h0,h1 are distinct halting states with no outgoing instruction. This is an effective Turing-complete register-machine presentation. Only the elementary effective compilation and finite runs are used below; no interpretation of an infinite arithmetic structure is assumed.

For each e we construct a closed pure typed sentence H_e. It says that P_e has a bounded trace ending in h0. Its time and value orders may be nonstandard or externally infinite. In particular, the definition does **not** assert that an internal chain is externally finite.

### 16.2 The explicit first-order trace template

All object variables in this template have the fixed type sigma. All predicates and graphs have types sigma→t or sigma→sigma→t, hence are admitted even when sigma=e. The template is ordinary first-order logic over a finite relational vocabulary, and H_e existentially quantifies every predicate in that vocabulary. Thus H_e is a pure typed sentence, uniformly computable from e.

Quantify unary predicates T,V; binary predicates <_T,<_V; endpoint variables a,b,z; one unary state predicate Q_q for each state q of P_e; and one binary register graph R_j for each register. For a unary domain D and strict order < define

    Next_D(x,y) := D(x) ∧ D(y) ∧ x<y ∧
                   ¬∃u(D(u) ∧ x<u ∧ u<y).

The conjunction inside H_e has the following clauses. Quantifiers displayed as ranging over a predicate domain are ordinary relativized sigma-quantifiers.

1. **Time.** T is nonempty, <_T is a strict linear order on T, a is its least element, b is its greatest element, and every t∈T other than b has an immediate successor: ∃u Next_T(t,u). A one-point interval a=b is allowed. No induction axiom is used.
2. **Values.** V is nonempty, <_V is a strict linear order on V, and z is its least element. No upper endpoint or global successor-existence axiom is needed.
3. **States and register values.** At every t∈T exactly one of the finitely many Q_q(t) holds. For every register j and t∈T there exists exactly one v∈V with R_j(t,v). The initial state Q_start(a) and initial register values R_j(a,z) hold.
4. **Final and halting conditions.** Q_h0(b) holds. At every t∈T distinct from b, neither Q_h0(t) nor Q_h1(t) holds. Together with state exclusivity this excludes Q_h1 everywhere and forbids continuation beyond either halting state.
5. **Instruction transitions.** For each instruction at state q and every Next_T(t,u), if Q_q(t), the state at u and all register graphs at t,u obey that instruction. For INC(j,q′), the old value v and new value w of register j satisfy Next_V(v,w), the other registers retain their values, and Q_q′(u). For DECJZ(j,q0,q1), if the old j-value is z, all values remain unchanged and Q_q0(u); otherwise the new value w satisfies Next_V(w,v), the other registers retain their values, and Q_q1(u). Each clause is a finite first-order formula, using the total functional R_j graphs to refer relationally to old and new values.

We may additionally stipulate that the orders, state predicates, and register graphs are false outside their designated domains; this is harmless and makes the finite witness specification literal. Strict linearity gives uniqueness of immediate predecessors and successors whenever they exist. No function type with individual output, Choice, Atomicity, Plenitude, modal principle, or illicit Logical Equivalence instance enters this construction.

### 16.3 Standard finite runs give the two required proof facts

**Lemma 16.1.** If phi_e(e) halts with output 0, then C+InfSchema_sigma proves H_e. A finite subset of the Infinity schema suffices.

Proof. Let the compiled program's actual run take k steps and let M be its largest register value along that run. Take k+M+2 pairwise distinct sigma-objects, using one schema instance. Define T to select k+1 of them and V to select the remaining M+1. Define their orders by finite disjunctions of equality pairs. Define Q_q to select exactly the time points where the actual finite run is in state q, and define R_j to select exactly the pairs giving the jth register value at each time. These are ordinary finite lambda abstractions; the empty disjunction gives an empty relation when appropriate. Set a,b to the first and last time points and z to the first value point. Every trace clause reduces to a finite equality calculation and the specified genuine transition. Thus the finitely many witness terms prove H_e in C. QED.

**Lemma 16.2.** If phi_e(e) halts with output 1, then C already proves ¬H_e.

Proof. Take the actual finite run, of length k, and reason from an arbitrary purported H_e witness. This is an external induction through the k standard transitions, producing a finite C proof, not internal induction over the witness's entire time order.

At stage zero the witness has its specified first time a, correct initial state, and all register values z. Maintain that the witness at the current time has the actual program state and register values represented by the corresponding finite initial segment of its value order. Immediate-successor uniqueness makes independently encountered representations of the same standard register value agree. The finite successor segment is strictly increasing, so its nonzero entries differ from z and every decrement from a positive represented value has the represented predecessor.

At every actual prehalting stage i<k, the actual state is nonhalting. Therefore the corresponding witness time is not b, since b has the unique state h0. The Time clause supplies its next time. The instruction clause forces exactly the actual next state and register values. If an increment needs a value successor that does not exist, that very clause contradicts the purported trace; otherwise it supplies the next value. If the necessary successor value has already appeared, uniqueness identifies it with the earlier representative. A zero test or decrement is fixed by the finite initial value segment. Thus premature exhaustion of time or values cannot yield a different run; it makes the certificate inconsistent.

After the k standard transitions the witness therefore has state h1 at a time in T. If that time is b, state exclusivity contradicts Q_h0(b); if it differs from b, the halting condition contradicts Q_h1 there. Thus no H_e witness exists. Every step is a finite first-order deduction over the displayed template, available in C, and the proof can be obtained effectively from the genuine finite halting run. QED.

The proof does not compare two arbitrary nonstandard computations. Such a comparison would require more work and is unnecessary. It also does not infer full internal Peano arithmetic from the weak Infinity schema.

### 16.4 Every complete solution computes binary DNR

Let T be any consistent theory extending C+InfSchema_sigma. Given a complete consistent pure extension Γ of T, define

    d_Γ(e) = 1 if H_e∈Γ, and 0 otherwise.

If phi_e(e)=0, Lemma 16.1 gives H_e∈Γ, so d_Γ(e)=1. If phi_e(e)=1, Lemma 16.2 gives ¬H_e∈Γ, so d_Γ(e)=0. Hence d_Γ is binary diagonally nonrecursive. The conversion is one fixed computable functional: compile e to H_e and ask one Γ-membership question. An adequate model code gives Γ by evaluation, so the same lower bound applies to every adequately presented model.

Binary DNR uniformly computes a complete consistent PA extension by the proof-search decision construction of §15.2, with PA as its fixed c.e. theory. Therefore every such Γ or model code has PA degree. This obtains a PA completion as an effective output; it does not assert that Γ's own Frege-number interpretation is a PA model.

### 16.5 Exact positive capacity, with only the schema

For each T among C, B, or F, add either InfSchema_e or InfSchema_t, or both. Optional strong Frege axioms and their boxed versions may also be required when consistent with the specified world cardinality. Then an oracle computes some countable adequate general model of this package **iff it has PA degree**. The lower bound is §16.4; the upper bound uses the fixed stronger Gallin construction satisfying both boxed Frege axioms and the ordinary PA-basis construction of §§7,13.3. When only e-Infinity is required, the witnessing Gallin model may have exactly two worlds. For t-Infinity use infinitely many worlds.

The corresponding Comp and Model solution sets are uniformly Medvedev-equivalent to PAcomp. For the direction from Comp to PAcomp, first use H_e to obtain binary DNR and then the fixed PA proof-search completion. For the reverse direction use the same fixed auxiliary Henkin model as before. As in §15, this produces some model of the required package and need not preserve an input completion's exact theory.

In particular, **even the weak Infinity schema excludes a computable adequate presentation**, although low adequate presentations still exist. Strong Infinity provides the clean Frege arithmetic interpretation; it is not the threshold at which the positive model-existence problem ceases to have a computable solution.

### 16.6 Robust Σ^0_1-completeness under every consistent c.e. strengthening

Let T be any consistent c.e. extension of C+InfSchema_sigma. Set

    V0={e:T⊢H_e},        V1={e:T⊢¬H_e}.

The sets are disjoint and c.e. by consistency. Lemmas 16.1–16.2 give K0⊆V0 and K1⊆V1, where Kb={e:phi_e(e) halts with output b}. The parameterized recursion argument of §14 now applies verbatim: compile p(n) to return 0 if n(n) halts and return 1 if p(n) is enumerated into V0, dovetailing the two searches. It gives

    n∈K  iff  p(n)∈V0  iff  T⊢H_{p(n)}.

Thus the closed pure theoremhood of every such T is Σ^0_1-complete. Here V1 consists of provable negations of H_e; no unproved global determinism theorem for arbitrary nonstandard trace orders is needed. The false case follows from the finite simulation lemma alone.

This extends the strong-Infinity preservation result in §14 to the weaker schema, and explains why computable pseudofinite positive examples cannot evade the adequate-presentation lower bound. Finite positive models remain computable when no Infinity schema is required.

## 17. Atomic diagrams of the explicit auxiliary Henkin models

There is a stronger presentation result for the **specific auxiliary first-order structures H_0,H_ch of §3**. It is not a claim about arbitrary action/category codes or arbitrary reducts of BBK models.

**Theorem 17.1.** Suppose M is an H_0-model and some fixed auxiliary type sort D_alpha is externally infinite. Every atomic-diagram presentation of M has PA degree. Consequently M has no computable atomic presentation. The conclusion already holds when the presentation supplies sorted domains, equality, the constants 0,1, and the application graphs; the complete elementary diagram is unnecessary.

An atomic presentation here gives effective sorted domain enumerations and decides atomic formulas in that first-order application language relative to its diagram oracle D. Application is total, so its values can be found by searching its D-decidable graph. The statement concerns the degree of a specified presentation, and the necessity of being PA is nonuniform in finitely many auxiliary parameters described below.

### 17.1 A fixed-variable family of computation certificates

Replace the separate zero-input programs P_e of §16 by one fixed universal register program U, whose first register is initialized to e and whose other registers are zero. U computes phi_e(e), entering h0 or h1 when the output is 0 or 1. Such a fixed finite program is obtained by the usual universal computation simulation. For an explicit reason that INC/DECJZ suffice, encode a Turing tape by two base-b integer stacks and a finite-control head symbol; loops of increments and zero-testing decrements implement multiplication/division by the fixed base b and addition of a digit, using finitely many temporary registers. A fixed universal Turing program therefore compiles to a fixed finite register program.

Use the trace template of §16 at the auxiliary sort alpha, with unary and binary predicates represented by sorts alpha→o and alpha→alpha→o. True atomic applications mean equality to 1. Initialize the first register at the value satisfying

    Dist_0(v) := v=z,
    Dist_(n+1)(v) := ∃u(Dist_n(u) ∧ Next_V(u,v)).

The formulas Dist_n express the nth immediate successor of the least value z. They have a uniform expansion using a fixed finite variable supply: in the recursive subformula, locally shadow names not free there; three temporary object names, in addition to the fixed endpoint parameter z, suffice. The standard Next formula uses a third temporary name for its intervening-point quantifier. Capture is avoided by this fixed recursive renaming convention.

Let G_e be the resulting closed auxiliary sentence for a trace ending in h0. Since U has fixed finite state and register sets, all G_e use one fixed finite relational vocabulary, one fixed finite list of sorts, and one fixed finite collection of variable names. Only formula length and quantifier nesting grow with e. Including several extra object-variable names for the other trace clauses gives one explicit fixed bound; its numerical optimum is immaterial.

The two proofs of §16.3 apply unchanged. If phi_e(e)=0, every H_0-model with infinite D_alpha satisfies G_e, because finitely many distinct elements and finite definable predicates witness its genuine run. If phi_e(e)=1, no H_0-model satisfies G_e: its Dist_e initialization specifies the unique finite successor chain up to e, and the standard finite simulation rules out any output-0 trace. In particular,

    e ↦ 1_{M satisfies G_e}

is binary DNR.

### 17.2 Finitely many represented Boolean and quantifier operations suffice

List all variable names used by the G_e family, assigning each its fixed auxiliary sort alpha_i, and put

    A = alpha_1 → ... → alpha_m → o.

An A-object represents a truth predicate on assignments to those variables. The full **definable** comprehension schema of §3 supplies the following finitely many objects:

- for each atomic formula pattern appearing in the G_e family, an A-object giving exactly its truth on assignments;
- a negation operator Neg:A→A and a conjunction operator Meet:A→A→A, acting pointwise;
- for each variable slot i, an operator C_i:A→A satisfying

      C_i(R)[x_1,...,x_m]=1
        iff ∀y∈D_(alpha_i) R[x_1,...,x_(i-1),y,x_(i+1),...,x_m]=1.

Every displayed type is admitted in the auxiliary language. For C_i, comprehension is applied to the first-order formula on the right, with R and the assignment tuple as parameters, and flattened through the final o output. The same construction supplies the finite atomic tables and Boolean operations. Extensionality identifies these as the required actual functions. This invokes only the stated syntactic comprehension schema, not an external full powerset or function space.

Choose one denotation for each of these finitely many objects and one element in each assignment sort. Their presentation indices form a finite tuple. A Turing program using D may hardcode this tuple. Given any G_e, it then evaluates its syntax bottom up: atomic formulas use their assigned tables, Boolean connectives use Neg and Meet, and a quantifier over variable i uses C_i (with existential quantification defined dually). Reused bound variable names cause no problem: the standard cylindrification semantics overwrites exactly that assignment slot within its scope.

The result is an A-object representing the truth of G_e on assignments. Since G_e is closed, apply it to the fixed dummy assignment tuple and compare its o-value with 1. Every operation performed is an application-graph computation or equality test relative to D. Thus D computes the DNR function in §17.1, proving Theorem 17.1.

### 17.3 Uniformity and the exact scope of the improvement

The finite operator indices are known to exist but need not be uniformly discoverable from an unexpanded atomic diagram. This does not affect the Turing-degree lower bound: finitely many indices can be built into a reduction for each presentation. Adding constants for that finite tuple does not change an individual diagram's degree. If the input presentation explicitly supplies those constants, the DNR extraction is uniform. No uniform extraction from every unnamed raw atomic code is asserted here.

For the auxiliary theories used to produce positive models with e-Infinity or t-Infinity, Theorem 17.1 combines with the earlier PA-basis upper bound: an oracle can compute an atomic presentation of some such auxiliary Henkin model iff it has PA degree. Some such presentations have low degree. With no Infinity requirement the finite-base full examples have computable atomic presentations.

This result does **not** automatically transfer to a reduct omitting the auxiliary sorts or their represented quantifier operators, nor to an abstract category/action presentation. The proof depends essentially on the existence of the finite assignment-predicate structure supplied by H_0's comprehension. The earlier adequate-code distinction remains necessary for unrestricted semantic-code claims.

## 18. Standard Frege arithmetic forces nonhyperarithmetical presentations

This strengthens the earlier true-arithmetic lower bound. It concerns **external standardness at the evaluation point**, not a new finitary axiom asserted to enforce standardness.

Write Std_sigma for the external condition that the current extension of N_sigma consists exactly of the distinct standard numeral denotations 0, Suc(0), Suc^2(0),... . The arithmetic premise used below is actual I_sigma (equivalently I*_sigma, by the recorded C theorem). No infinitude of the actual counting domain is needed once this premise is given. Weak Infinity at sigma together with Std_sigma is one sufficient way to obtain it.

**Theorem 18.1.** If a C-model satisfies I_sigma and Std_sigma at its evaluation point, its complete actual pure theory is not hyperarithmetical. More strongly, that theory computes every hyperarithmetical set, with the reduction allowed to depend on the set. Every adequate truth-evaluable presentation has the same lower bound. The conclusion therefore also holds under InfSchema_sigma + Std_sigma.

**Theorem 18.2.** For the explicit auxiliary H_0/H_ch models of §3, if an associated Gallin model satisfies I_sigma + Std_sigma at any world, then every atomic-diagram presentation of the auxiliary structure is nonhyperarithmetical. In particular this holds with an infinite sigma-domain and Std_sigma. Thus a hyperarithmetical atomic presentation with an infinite counting domain must have nonstandard Frege numbers at every world.

### 18.1 The exact arithmetic interpretation at a standard point

Under I_sigma, Goodsell's interpretation cited in §13 supplies Peano arithmetic. Since its number domain consists exactly of the standard numerals, its zero and successor, and hence its Sum and Prod relations, are the standard ones. More explicitly, the PA recursive equations and an external finite induction determine addition and multiplication on every pair of standard numerals. No cardinal realization or actual counting-domain infinitude is needed for this argument.

For the sufficient condition InfSchema_sigma + Std_sigma, the quantified Frege Axiom of Infinity holds at the point: every current N-number is a standard numeral, and a standard finite numeral cannot count an externally infinite domain. Section 13.1 then gives I_sigma. This is a separate route to the arithmetic premise, not a further assumption in Theorem 18.1.

Let nu=(sigma t)t. For each current property X of type nu→t, take its actual extension on the numerical domain:

    A_X := {n∈N : X(numeral n) is actually true}.

Let S be the collection of these subsets of the external natural numbers. Distinct property intensions may yield the same subset; the interpreted second-order set equality is equality of these extensions, not identity of the original properties. Set quantification over S is therefore represented by original quantification over all X, with repeated extensions harmless.

Then (N,S,+,×,0,1) is an omega-model of full second-order comprehension. To verify this explicitly, translate any second-order formula phi(n,X_1,...,X_k): numerical quantifiers are restricted to N_sigma, set membership becomes application, and set equality becomes coextension on N. Its translated matrix is an available original formula. The lambda term

    Y := lambda n . N(n) ∧ phi^#(n,X_1,...,X_k)

has exactly the requested current extension. This works with arbitrary set quantifiers and parameters, because comprehension is ordinary typed lambda formation. Induction is true for every interpreted formula because the numerical domain is externally the standard natural numbers. No external powerset fullness and no higher-order Choice are inferred.

Here and below N(n) denotes N_sigma(n), with n of numerical type nu.

### 18.2 A primary-source fixed-point obstruction

The external computability input is Vassilios Gregoriades, *On a Question of Jägers*, arXiv:1905.09609v2, revised 1 March 2022, Theorem 1, printed pp.2–3: there is a fixed positive arithmetic formula psi(n,R) whose associated monotone operation on subsets of N has **no hyperarithmetical fixed point**. Lemmas 13–14, pp.7–8, show more precisely that every fixed point has columns representing every hyperarithmetical set. The relativization discussion on p.4 supplies the corresponding statement relative to any real parameter. Primary source checked directly: https://arxiv.org/abs/1905.09609v2 and https://arxiv.org/pdf/1905.09609 . This is an imported theorem, not a new result attributed to the present notes.

We now show directly that the interpreted omega-model contains an actual fixed point of this operator. This avoids presuming that the restricted collection S is an externally complete lattice.

For X∈S put Phi(X)={n:psi(n,X)}. Arithmetic comprehension gives Phi(X)∈S. Arithmetic truth with a set parameter is absolute between (N,S) and the external universe, and positivity makes Phi monotone externally. Say Pref(X) iff Phi(X)⊆X. The full comprehension instance

    L = {n : ∀X∈S (Pref(X) → n∈X)}

puts L in S. For every prefixed X, L⊆X, so Phi(L)⊆Phi(X)⊆X. Thus Phi(L)⊆L. By monotonicity Phi(Phi(L))⊆Phi(L), so Phi(L) itself is an available prefixed set. The definition of L now gives L⊆Phi(L). Hence L=Phi(L).

This proves that L is an **external** fixed point of Gregoriades' arithmetic operator. It need not be the least fixed point among all external subsets of N: the intersection used only available prefixed sets. The source theorem applies to every fixed point, so L is nonhyperarithmetical regardless.

Moreover L is represented by a fixed **pure original term**:

    lambda n . N(n) ∧
      ∀X^{nu t}[(∀m (N(m) ∧ psi^#(m,X) → X(m))) → X(n)].

All arithmetic in psi^# is translated using the fixed pure N, Sum and Prod definitions. There are no model-specific parameters in this term. The interpretation of the source formula remains positive in X, and all auxiliary coding relations for finite computations are ordinary arithmetic relations on the standard numerical domain.

### 18.3 Extracting the lower bound from the precise codes

Given the complete actual pure theory Γ, compute L by querying whether the closed pure sentence L(numeral n) belongs to Γ. Thus L≤_TΓ. Since L is nonhyperarithmetical and the hyperarithmetical sets are closed downward under Turing reducibility, Γ is nonhyperarithmetical. This proves the first assertion of Theorem 18.1 without access to a semantic truth predicate inside the object theory.

For the stronger assertion, Lemmas 13–14 of the cited paper say that for every hyperarithmetical A there is a standard column index a such that

    n∈A iff pair(a,n)∈L.

The ordinary computable pairing map and this fixed index a give A≤_TL≤_TΓ. This is an individual Turing reduction for each A, not a claim of a computable enumeration of all hyperarithmetical sets or a uniform system of valid ordinal notations. The corresponding column also belongs to S by arithmetic comprehension, so the omega-model contains every hyperarithmetical set. This containment has been justified by the cited primary theorem and the explicit fixed-point construction, rather than inferred merely from closure under finitely many jumps.

For Theorem 18.2 let D be an atomic diagram of the auxiliary structure. Hardcode the finitely many indices of the pure zero, successor and L denotations, and the chosen world w. Starting from zero, auxiliary application computes each numeral. Applying L to that numeral and then to w produces its o-value, which is compared with 1. Thus D computes L. This uses application and equality only, with the same legitimate nonuniform finite-parameter convention as §17; no complete elementary diagram is needed. The same argument computes each hyperarithmetical set through its column of L.

### 18.4 Consequences and limits

The earlier Low Basis models have nonstandard arithmetic for a stronger reason than merely failing to compute true first-order arithmetic: **no hyperarithmetical adequate standard-arithmetic code exists at all**. This includes every low positive presentation and every presentation computable in a fixed finite Turing jump.

The statement does not assert that such codes compute Kleene's O. Being a Turing upper bound of every hyperarithmetical set, with separate reductions, is different from uniformly deciding all recursive ordinal notations or all recursive-tree well-foundedness questions. Section 19 supplies strictly sub-O standard positive models and an exact common-information statement, without claiming an exact presentation spectrum.

The lower bound also applies to any hypothetical standard-N_sigma point of Max_C or Strong Possibility: these imply I_sigma. In particular it does not require actual individual infinitude and is compatible as a conditional claim with SP's individual monism. No existence of a standard-arithmetic SP model follows from the positive examples or the basis argument below.

Standard-arithmetic countable general Gallin models nevertheless exist. Start with a full hierarchy over E=N and either W={0,1} or W=N, and take a countable elementary substructure of the auxiliary first-order structure. All pure numeral denotations are retained (or may explicitly be included among the countably many initial parameters), and no nonnumeral can newly enter the first-order-definable N extension by elementarity. The resulting general model has standard Frege numbers and the relevant positive/Infinity properties. Its presentation must therefore be nonhyperarithmetical.

As an independent source cross-check of the omega-model perspective, Denis Hirschfeldt's author-hosted *Slicing the Truth*, §10.3, printed pp.166–167 in the 199-page version, states that Pi^1_1 comprehension proves arithmetical transfinite recursion and that every omega-model of ATR_0 contains all hyperarithmetical sets: https://www.math.uchicago.edu/~drh/Papers/Papers/rm.pdf . The proof above does not rely on importing either assertion; it uses the explicitly verified omega-model interpretation and Gregoriades' fixed-point theorem.

## 19. Standard positive models below Kleene's O; their exact common information

The lower bound in §18 is compatible with substantial variation in the codes of standard-arithmetic models. This section gives an upper bound and a precise common-information theorem. It concerns the consistent positive packages C, B and F, with either e-Infinity and two worlds or both e,t-Infinity and infinitely many worlds. It does not assert the existence of a standard-arithmetic Strong Possibility model.

### 19.1 An explicit arithmetical class of standard Henkin codes

Fix the c.e. auxiliary theory U of §5.1 or §5.2, choosing H_ch so that its Gallin models satisfy the strongest positive package F. Add definitional constants for the finitely many original pure terms 0_sigma, Suc_sigma and N_sigma at each counting type whose arithmetic is required to be standard. Their translated denotations exist uniquely by comprehension and extensionality, so this is a conservative c.e. definitional expansion. The world constant w0 is already present. Then perform the fixed Henkin expansion of §6, and let U^H be the resulting consistent c.e. theory.

A complete consistent Henkin code D supplies a characteristic function for its sentences. For each closed term u of the numerical sort nu* impose

    [N_sigma(u)(w0)=1 belongs to D]
        implies exists standard n [u=numeral_sigma(n) belongs to D].    (19.1)

Here numeral_sigma(n) is the computably generated closed auxiliary application term Suc_sigma^n(0_sigma). Thus (19.1), simultaneously for all u, is a Pi^0_2 condition on D. We may require it for every closed world term w instead of just w0; this remains Pi^0_2. We may also require it at both sigma=e,t when using the infinite-world theory. The corresponding strong Infinity axioms guarantee that the numeral denotations are pairwise distinct. In the term model every element is denoted by a closed term, so (19.1) says exactly that the Frege number extension has no nonnumeral elements at the specified worlds and counting types.

Let K be the class of complete consistent Henkin codes for U^H obeying these conditions. Completeness, consistency and containment of U^H are Pi^0_1 conditions in the standard decision coding; adjoining (19.1) makes K a lightface Pi^0_2 class, and in particular a lightface Sigma^1_1 class.

The class K is nonempty. Start with the full auxiliary hierarchy over E=N, using W={0,1} for the first package or W=N for the second. Its Frege arithmetic is standard at every applicable world and counting type by §5. Interpret the fresh Henkin constants successively by actual witnesses in that full structure. Its complete theory in this countable expanded language lies in K. The associated countable term model retains standard arithmetic by (19.1). No effectiveness of the full structure's truth set is asserted.

From any D in K the construction in §§6–7 computes a countable auxiliary elementary diagram, a truth-evaluable Gallin model code, and its complete actual pure theory. All three transformations are fixed computable functionals. Their output structures satisfy F and the displayed strong Infinity axioms, and hence also all weaker positive packages under consideration.

### 19.2 The basis theorems used

The external computability input is Leo Harrington, Richard A. Shore and Theodore A. Slaman, *Sigma^1_1 in every real in a Sigma^1_1 class of reals is Sigma^1_1*, author-hosted draft dated 11 July 2016, https://math.berkeley.edu/~slaman/papers/Sigma1116.pdf . The following statements were checked directly in that source:

- Theorem 2.9, printed p.7: every nonempty lightface analytic class has a member recursive in Kleene's O and of strictly smaller hyperdegree; it may be chosen with omega_1^D=omega_1^CK.
- The Kreisel basis consequence of Theorem 2.1, explained on p.2: given any nonhyperarithmetical X, such a class has a member D with X not hyperarithmetical in D.
- Theorem 2.6, printed p.6, permits simultaneous avoidance of any countable family of nonhyperarithmetical reals.

Only these basis statements are imported; the class K and its interpretation into the present model problem have been constructed explicitly above. The source's stronger descriptive-set-theoretic results are not needed.

### 19.3 A nonhyperarithmetical standard code strictly below O

Apply Theorem 2.9 to K. Choose D in K with D recursive in O and O not hyperarithmetical in D. Let Q be any of the auxiliary elementary-diagram, auxiliary atomic-diagram, adequate Gallin-model, or complete pure-theory outputs of §19.1. Then Q is Turing reducible to D. By §18, Q is nonhyperarithmetical. Consequently

    Q is nonhyperarithmetical,       Q <_T O,
    O is not hyperarithmetical in Q, and omega_1^Q=omega_1^CK.       (19.2)

The strict Turing inequality follows because Q≤_TD≤_TO, whereas O≤_TQ would contradict O not hyperarithmetical in D. The ordinal equality follows from omega_1^CK≤omega_1^Q≤omega_1^D=omega_1^CK.

Thus standard positive models need not compute Kleene's O. They may nevertheless compute every hyperarithmetical real individually, as §18 proves. There is no conflict: the reductions to individual hyperarithmetical reals need not be uniformly enumerable from valid ordinal notations.

The sub-O models are not asserted to be elementary submodels of the full standard witnesses used to establish nonemptiness. Indeed the branch formulas P_e of §21.2 have their correct external Sigma^1_1 truth values in every such full witness: every external branch graph is available there. Its complete pure theory therefore computes O, and any elementary reduction retaining that theory does too. A sub-O standard model must instead fail some P_e whose recursive tree really has a branch. Such a failure says that no branch is represented in its available relation domain; it does not make its externally standard arithmetic nonstandard. The same distinction applies to the standard full coalesced Max root and the sub-O standard Max models of §20, by `max-degree.md` §13.

### 19.4 Exactly the hyperarithmetical reals are common to all solutions

Fix one of the positive packages above with standard arithmetic imposed externally at an infinite counting type. Let Sol be either its complete actual pure theories, its countable adequate model codes, or the atomic/elementary diagrams of the explicit auxiliary realizations. For the auxiliary case, fix H_0 or H_ch and the same positive cardinality/Infinity requirements. Then, for every real X,

    [for every Q in Sol, X≤_TQ]  iff  X is hyperarithmetical.       (19.3)

The forward-to-hyperarithmetical implication uses the basis theorem. If X is not hyperarithmetical, choose D in K such that X is not hyperarithmetical in D. The corresponding output Q belongs to Sol and is computable from D. Therefore X is not even hyperarithmetical in Q, and in particular X is not Turing reducible to Q. For H_0 the same H_ch witness is an allowed stronger realization. Conversely, §18 shows that every Q computes every hyperarithmetical X, with a reduction depending on X and, for unnamed atomic presentations, finitely many presentation indices.

In fact (19.3) remains true when its left side is weakened to “X is hyperarithmetical in every Q.” For any countable sequence of nonhyperarithmetical reals X_i, Theorem 2.6 gives one D in K, and hence one output Q, such that none of the X_i is hyperarithmetical in Q. These are existence claims; no uniform algorithm for choosing the avoiding solution from a description of X is asserted.

Two consequences make the scope of the computational distinction precise. First, Sol has no least Turing degree and no least hyperdegree. A least solution degree would be common to every solution, hence hyperarithmetical by (19.3) or its hyperarithmetical variant, contradicting §18. Second, the class of oracle degrees capable of computing some standard positive solution has no least degree, so it cannot be the upper cone above one fixed oracle degree. These statements concern the whole solution problem, not the spectrum of any prescribed isomorphism type.

The arbitrary-Henkin task and the externally-standard task are therefore sharply different. The former has low solutions and the PA-degree capacity of §16. The latter has no hyperarithmetical solution, has solutions strictly below O, and has exactly HYP as the information shared by all solutions. An exact classification of all oracle degrees solving the latter task is not claimed.

## 20. The standard-model basis theorem extends to hyperarithmetical theories

The positive auxiliary structures were useful explicit witnesses, but the basis argument is more general. Use the original BBK interpretation-and-truth code and complete witness theories described in `max-degree.md` §§5,9. This is the countable term-model construction in Bacon–Dorr, *Classicism*, accessible 1 July 2022 draft, §3.1, Theorem 3.2 and n.64, printed pp.44–45. It is not an extensional Henkin representation of Max.

**Theorem 20.1.** Fix a theory T whose axioms are computably enumerable in some hyperarithmetical oracle A, and suppose its consequences contain C+I_sigma. If T has a model with externally standard N_sigma at its actual point, then:

1. T has a countable adequate standard-N_sigma BBK model with a nonhyperarithmetical code Q satisfying Q<_TO, O not hyperarithmetical in Q, and omega_1^Q=omega_1^CK. Its complete actual pure theory can be chosen with the same properties.
2. For its complete actual pure theories and its adequate standard-model codes, exactly the hyperarithmetical reals are Turing reducible to every solution. The same holds with hyperarithmetical reducibility in place of Turing reducibility.
3. Neither solution problem has a least Turing degree or least hyperdegree. For any countable family of nonhyperarithmetical reals, one standard solution avoids all of them even under hyperarithmetical reducibility.

**Proof of the code-class claim.** Expand the typed language by fresh constants in a fixed witness schedule. Include the corresponding Henkin axioms for all formulas of the successive expanded languages, and C for that expanded language. Keep the optional axioms of T and any reference-theoremhood side conditions in their original specified language; adding constants does not enlarge Max's reference scheme. This gives an A-c.e. witnessed theory T^H.

Let K_T consist of its complete consistent decision codes D such that, for every closed numerical term u in the expanded language,

    Nu belongs to D  implies  exists standard n [u=numeral_sigma(n) belongs to D].

The completion condition is Pi^0_1(A), and the displayed standardness condition is Pi^0_2 in D. Hence K_T is arithmetical relative to the hyperarithmetical parameter A, and therefore is lightface analytic. No uniform hyperarithmetical bound for a varying presentation of T is being asserted; T and A are fixed.

A standard-N_sigma model of T expands successively to the witness constants by actual witnesses. Its complete expanded-language theory lies in K_T. This establishes nonemptiness directly from standard-model existence, a stronger hypothesis than consistency alone. Conversely every D in K_T has the usual BBK term model: quotient closed terms by the identities in D, choose least-coded representatives, evaluate terms by substitution, and decide actual truth by membership in D. Every numerical object in this model is a term denotation, and the displayed condition makes it a standard numeral. Since T entails I_sigma, those numerals are distinct and the arithmetic is standard. These model and pure-theory outputs are computable from D.

Now apply the same HSS basis and avoidance theorems as in §19, and the lower bound of Theorem 18.1. The proofs of all three conclusions are exactly the reductions in §§19.3–19.4. QED.

For a code supplying only application, equality and actual truth valuation, the lower bound is still available nonuniformly: hardcode the indices of zero, successor and the pure fixed-point term L of §18. Application computes the numerals and L's truth values. The adequate-code outputs above also supply these weaker data, so the same existence and common-information statements hold for this specific encoding. A bare action/category code without actual valuation remains outside the claim.

### 20.1 Old Max versus conditional Strong Possibility and limit theories

The standard coalesced-root Max construction verified in `max-degree.md` §10.1 has externally standard N_e. Since old Max is 0′-c.e., Theorem 20.1 applies **unconditionally** to the standard-N_e Max model problem. Standard Max therefore has nonhyperarithmetical solutions strictly below O, exactly HYP as common information, and no least solution degree. This is compatible with all Max codes having PA degree relative to 0′: externally imposing standardness gives a stronger, different solution problem.

Strong Possibility is 0′′-c.e., and the conditional omega-stage theory in `limit-possibility-degree.md` is 0^(omega)-c.e.; these are hyperarithmetical axiom oracles. Thus Theorem 20.1 applies to either theory **if a standard-N_sigma model exists**. Neither ordinary consistency nor the positive standard-model construction proves that extra existence assertion. In particular, the conditional SP application does not assume an infinite actual individual domain.

### 20.2 Finitary compactness always supplies a nonstandard model

No consistent finitary pure theory T extending C+I_sigma can have only standard-N_sigma models, **regardless of the complexity of its axiom set**. Add one fresh numerical constant c and the assertions Nc and c≠numeral_sigma(n) for every standard n. Every finite subset is satisfied by expanding any T-model with c interpreted as a sufficiently large standard numeral: I_sigma makes all those numerals distinct. Finitary Henkin/BBK compactness therefore gives a model of the entire extension. Its c is an actual N-number distinct from every standard numeral. The original reference language in any Max/SP side condition is kept fixed; the new witness constant does not enlarge that scheme.

Under the hyperarithmetical axiomatization hypothesis of Theorem 20.1 there is a stronger effective conclusion. Relative Low Basis applied to its A-c.e. witness theory gives a complete witness code D with (D join A)′ equivalent to A′. In particular D≤_T A′, so D is hyperarithmetical. Its BBK term model has a hyperarithmetical adequate code. Theorem 18.1 therefore forces its N_sigma to be nonstandard. Thus effectivity is needed for this low-complexity witness, not for the bare impossibility of forcing external standardness by a consistent finitary theory.

This statement concerns the actual number domain. It does not deny that a theory can have both standard and nonstandard models; Theorem 20.1 describes the standard part when nonempty. It also keeps the external standardness condition separate from any proposed finitary or infinitary axiom scheme intended to approximate it.

### 20.3 The standard solution problem is strictly harder

Under Theorem 20.1's nonempty-standard-model hypothesis, let Model(T) be the unrestricted adequate-model problem and Model_std(T) its standard-N_sigma subproblem. Forgetting the standardness requirement is the identity transformation, so Model(T) is Medvedev reducible to Model_std(T).

The reverse reduction is impossible. Section 20.2 supplies a hyperarithmetical unrestricted solution Q. If a computable functional converted every unrestricted solution into a standard one, its output on Q would be hyperarithmetical, contradicting §18. The same contradiction works even if the proposed functional is allowed any one fixed hyperarithmetical oracle: its output on the hyperarithmetical Q remains hyperarithmetical. Thus

    Model(T) <_M Model_std(T),

and no hyperarithmetical uniform standardization procedure exists. The identical argument applies to complete pure theories, where the standard subproblem consists of those theories realized at a standard-N_sigma model. This is a comparison of solution tasks, not an assertion that one can recognize standardness from an arbitrary model code.

## 21. Finite-condition satisfiability with standard numbers is analytic-complete

This section concerns **semantic validity in a restricted standard-model class**, not finitary theoremhood of the original c.e. positive theories. Keep the explicit auxiliary H_0 or H_ch model presentation. Fix either the two-world package with individual Infinity, or the infinite-world package with both base-type Infinity axioms, as in §19. Require standard N_e at the actual world; imposing standardness at every world or also at N_t in the infinite-world case gives the same conclusions below. Write G_std for this specified class of countable general Gallin models.

For a closed pure original sentence P, set

    Sat_std(P) iff some M in G_std satisfies P,
    Val_std(P) iff every M in G_std satisfies P.

**Theorem 21.1.** Sat_std is Sigma^1_1-complete and Val_std is Pi^1_1-complete under ordinary computable many-one reductions. This holds for each of the H_0 and H_ch versions and both indicated world/Infinity packages. The complete code class from §19 is arithmetical; existentially asking for a member satisfying a given finite condition is nevertheless an analytic-complete decision problem.

### 21.1 The analytic upper bound

Use the class K of complete standard Henkin codes in §19, with H_0 instead of H_ch when appropriate. The recursive translation of P supplies an auxiliary sentence P*(w0). Then

    Sat_std(P) iff exists D in K [P*(w0) belongs to D].

The right side existentially quantifies one real over an arithmetical condition, so it is lightface Sigma^1_1. A model in the class can be expanded by Henkin witnesses without changing its standard numerical domain, so both directions of this equivalence hold. Since Val_std(P) iff not Sat_std(neg P), the validity set is Pi^1_1.

### 21.2 The lower bound uses infinitely branching recursive trees

Use the standard lightface analytic normal form: fix a Sigma^1_1-complete set S and a recursive predicate R such that

    e in S iff exists f:N→N forall s R(e,f restricted to s,s).      (21.1)

Finite sequences are coded by ordinary natural numbers. Equivalently one can use the existence of a path through a uniformly recursive tree on N^{<N}. The trees are not restricted to binary or finitely branching trees. The recursive analytic normal form is stated in the introduction, printed p.1, of the HSS primary source cited in §19.2; only that standard form is used here.

Let nu=(et)t. For a property F of admitted type nu→nu→t, let Fun_N(F) say that its actual extension on N_e×N_e is a total single-valued relation. Let Prefix(F,s,c) be the arithmetical formula saying that c codes a sequence of length s and, for each i<s, its ith entry is the unique m with F(i,m). These are ordinary finite formulas using the interpreted arithmetic; original quantifiers over numerical variables are restricted to N_e.

Translate the fixed recursive predicate R into its standard arithmetical defining formula R^#. Define the closed pure sentence, effectively from e,

    P_e := exists F^(nu nu t) [Fun_N(F) and
             forall s in N_e exists c in N_e
               (Prefix(F,s,c) and R^#(numeral e,c,s))].           (21.2)

In any C+I_e model with standard N_e, the actual extension of an F witnessing (21.2) is an external total function f:N→N. Standard arithmetic makes the Prefix and R clauses absolute, so that external f satisfies (21.1). Therefore a G_std model of P_e implies e in S. This direction needs neither a full set domain nor Choice; it reads an existing relational witness at a standard numerical domain.

Conversely, if e in S, choose one actual f satisfying (21.1). In the full auxiliary hierarchy over E=N and the stipulated world set, represent its graph on the standard numeral objects by a relation that is constant across worlds, taking bottom off that numerical graph. Fullness supplies this relation, and the full hierarchy satisfies P_e and all the required positive/Infinity axioms, with standard Frege arithmetic. Expanding it by Henkin witnesses yields a code in K satisfying P_e, and hence a countable standard general Gallin model. This use of fullness is solely an existence witness; the resulting countable model is not claimed to be full.

We have proved e in S iff Sat_std(P_e). Thus Sat_std is Sigma^1_1-hard, and computable negation gives Pi^1_1-hardness of Val_std. Together with §21.1 this proves the theorem.

### 21.3 Identity fragments and the distinction from the original theory

Every model under consideration satisfies B and therefore the recorded No Pure Contingency theorem. For closed pure P, its actual truth is equivalent to the pure identity P=top. Hence the same exact completeness levels already hold when the finite conditions, or the validity queries, are restricted to closed pure identities.

These are not new complexity bounds for ordinary B or F theoremhood: those remain Sigma^0_1-complete as shown earlier. External standardness changes the semantic class. No extra finitary axiom, no change to C's Logical Equivalence rule, and no change to old Max's reference theory has been made.

### 21.4 Robust failure of hyperarithmetical effective axiomatization

Let V_std be the entire closed pure validity theory of G_std. No consistent theory whose consequences contain V_std can be computably enumerable in a hyperarithmetical oracle. This is stronger than saying that V_std itself is not hyperarithmetical, and needs an additional argument.

Use the fixed pure L of §18. Gregoriades' Lemmas 13–14 give, for every hyperarithmetical real A, an index a depending only on A such that **every** external fixed point Q of the fixed operator has its a-column equal to A. In particular the same index a works for L in every standard model of the present class. Thus, for every n, exactly the correct member of the pair

    L(numeral pair(a,n)),       neg L(numeral pair(a,n))

belongs to V_std. The index a need not be computably obtainable from an arbitrary description of A; it is a fixed finite parameter for the reduction for that A.

Suppose U is a consistent X-c.e. theory containing all these validities. Enumerate its proofs and race the two displayed literals. The correct literal eventually appears, and consistency excludes the incorrect one. Consequently A≤_TX for every hyperarithmetical A. If X were hyperarithmetical, its jump X′ would also be hyperarithmetical; taking A=X′ contradicts X′ not Turing reducible to X. Hence X cannot be hyperarithmetical.

This does not prohibit consistent extensions below O. Section 19 supplies a standard model whose complete pure theory is a nonhyperarithmetical real Q<_TO; that complete theory contains V_std and is trivially Q-c.e. Thus the obstruction is to all hyperarithmetical enumeration oracles, not a claim that every consistent extension must compute O or the whole Pi^1_1-complete validity set.

### 21.5 The same bounds hold for the unrestricted standard positive classes

The explicit auxiliary presentation in Theorem 21.1 is useful but not essential to its conclusion. Take all standard-N_e models of B or F, with I_e, quantified individual Infinity, or either of the stronger positive Infinity packages used above. Their finite-condition satisfiability is Sigma^1_1-complete, and their validity is Pi^1_1-complete, again already for closed pure identities.

For the upper bound, use the original-language BBK witness coding of §20 instead of the auxiliary H_0/H_ch coding. The original axiom theory is c.e. and the standardness condition on its witnessed numerical terms is arithmetical, so existence of a standard code satisfying the finite condition is Sigma^1_1. Every standard model can be expanded by witnesses and reduced to the countable witnessed model while preserving its standard numerical domain. For the lower bound, the full standard Gallin witnesses in §21.2 are members of these broader classes and realize every external numerical branch graph. Conversely, in any standard-N_e member, a relation witnessing P_e still yields an external branch by exactly the absolute-arithmetic argument there. Thus enlarging the class neither destroys the reduction nor changes the upper bound. No Pure Contingency supplies the identity-fragment assertion.

More generally, the sentence-fragment argument applies to any fixed hyperarithmetically enumerable T extending C+I_e whose standard models can realize every external branch graph used in (21.2). It is enough to have one standard T-model in which every external numerical binary graph is an available relation. The analytic upper bound comes from §20, and that one model supplies all positive instances of the lower reduction. The identity-fragment conclusion additionally requires the relevant equivalence between actual pure truth and identity with top. The original standard Max construction satisfies the branch-graph hypothesis but does not have this equivalence; its contrasting identity fragment is treated separately in `max-degree.md` §13.

## 22. Original application-and-equality codes

Section 17 gave a lower bound for explicit auxiliary structures. There are also direct results for the **original** sorted applicative algebra, with no auxiliary sorts in its code. Ordinary PA degree already follows from possible weak Infinity; Actuality is additionally useful for recovering the entire actual valuation and for the standard-number lower bound. This section distinguishes those hypotheses and the coding information precisely.

An original applicative equality presentation supplies numbered sorted domains, decidable current identity, and the graphs of original application, uniformly relative to its diagram oracle D. Total application is then D-computable by search. It does not by definition supply actual truth, a uniform denotation function for every lambda term, or the indices of all logical operators. Finite indices may be hardcoded for an individual degree reduction; uniform extraction requires that the corresponding finite tuple be provided.

### 22.1 Actuality recovers actual valuation

**Lemma 22.1.** In a C+Actuality model, an original applicative equality presentation computes its entire actual truth valuation, nonuniformly in finitely many indices.

Choose an Actuality witness a, so a is actually true and every actually true p satisfies a≤p. Let Meet denote the pure propositional conjunction operation. The Boolean identities of C give

    p is actually true iff a≤p iff Meet(a,p)=a.                   (22.1)

For the reverse implication in the first equivalence, a≤p implies Box(a→p); T and actual a imply actual p. The second equivalence is the ordinary Boolean order identity. Hardcode the indices of a and Meet, apply Meet twice in its curried presentation, and use identity to test (22.1). This works for every proposition object, not merely for pure formulas.

The witness a need not be uniformly recoverable from unnamed application/equality data. Adding constants for this finite tuple does not change an individual presentation's Turing degree. No universal term evaluator is obtained just from this lemma; the following lower bounds use explicitly fixed finite term families.

### 22.2 Possible weak Infinity already forces PA degree in the original algebra

**Theorem 22.2.** Every original applicative equality presentation of a C-model satisfying every Diamond AtLeast_n(sigma) has PA degree. Actual weak Infinity at sigma suffices; Actuality is not required.

Use the fixed universal-register-program trace family from §17.1, now in the **original** language at sigma. It has a fixed finite list of variable names x_1,...,x_m of fixed original types alpha_1,...,alpha_m. These include the state and register predicate variables; all their types are admitted. Only the length of the Dist_e formula grows with e. Write H_e for the resulting closed pure trace sentence. When phi_e(e)=0, §16 gives a genuine C theorem AtLeast_n(sigma)→H_e for a suitable finite n; the possible lower bound therefore gives Diamond H_e. When phi_e(e)=1, the finite-prefix argument gives the genuine C theorem neg H_e.

Put A=alpha_1→...→alpha_m→t. The following are fixed finitely many **pure original lambda terms**:

- each atomic-pattern table lambda x_1...x_m . theta(xbar) for an atomic pattern appearing in the trace family;
- Neg_A= lambda R xbar . neg R[xbar];
- Meet_A= lambda R S xbar . (R[xbar] and S[xbar]);
- C_i= lambda R xbar . forall y^alpha_i R[x_1,...,x_(i-1),y,x_(i+1),...,x_m].

All their output types end in t. In particular no individual-output function or product type has been introduced. These are original terms, so their denotations exist in every C-model; no auxiliary comprehension or full external function space is used.

Hardcode their indices and one dummy element of each assignment sort. Evaluate the finite syntax of H_e bottom up by application, exactly as in §17.2. Reusing variable names is handled by the corresponding cylindrifier C_i. The resulting A-object is the denotation of lambda xbar . H_e. This claim is about denotations, not merely current coextension: it follows recursively by beta conversion and capture-avoiding substitution in the displayed term definitions. Because H_e is closed, applying to the dummy assignment returns the very proposition denoted by H_e, independently of those dummy objects.

Hardcode bottom as one further finite index and test whether the resulting proposition is distinct from it. In C, p=bottom is equivalent to Box neg p. Consequently Diamond H_e makes H_e nonbottom in the output-0 case. In the output-1 case, necessitating the genuine C theorem neg H_e makes H_e literally bottom in every C-model. Thus

    d(e)=1 iff the computed H_e object is not bottom

is binary DNR. This proves Theorem 22.2 without computing actual valuation. This strengthening was proposed by the maximalist-model lane and independently checked here. The distinction between an actual refutation and a genuine C refutation is essential: the latter is why the output-1 proposition is bottom at every point.

For any fixed consistent c.e. theory T extending C plus this possible weak-Infinity schema, an oracle computes some countable original applicative equality presentation of a T-model **iff it has PA degree**. Necessity is Theorem 22.2. For sufficiency, a PA oracle chooses a complete consistent witnessed extension of T and the standard BBK term construction supplies an adequate code, hence its application/equality reduct. The finite indices in the lower bound make this an oracle-capacity statement; no uniform Medvedev equivalence for arbitrary unnamed reduct codes is claimed.

If I_sigma is assumed instead of weak Infinity, an easier DNR extraction avoids the syntax compiler. Hardcode zero, successor, bottom and the single pure operation G= lambda n . (I_sigma and HaltOutput0(n)). A real output-0 computation makes G(numeral e) actually true under I_sigma, hence nonbottom. A real output-1 computation gives the genuine C theorem I_sigma→neg HaltOutput0(numeral e), so G(numeral e)=bottom. The same nonbottom test gives binary DNR directly. Alternatively, under Actuality one can use actual valuation and the operation without the I_sigma conjunct.

This ordinary-PA argument does not yield PA degree relative to 0′ for a bare Max applicative equality presentation. The negative oracle-run facts used for that stronger diagonalization are Max theorems rather than genuine C theorems; necessitating them would be illegitimate. The separate bare Max lower bound remains 0′, and adding actual valuation gives the stronger relative-PA bound.

Consequently a C-model with a computable bare applicative equality presentation has some necessary finite bound at every type. This does not by itself make the bounds or exact sizes uniformly recursive, or supply a complete term interpreter: those stronger conclusions in §23 concern c.e. complete pure theories. See `effective-refinements.md` §9.4 for this reduct-code corollary and its scope.

### 22.3 The standard-number lower bound also transfers

Suppose a C+Actuality+I_sigma model has externally standard N_sigma. Hardcode the indices of zero, successor and L from §18, in addition to the Actuality/Meet tuple. Application computes L(numeral n), and (22.1) computes its actual truth. Thus its original applicative equality diagram computes the external fixed point L and every hyperarithmetical real individually. It is nonhyperarithmetical.

When the standard model classes in §§19–20 additionally satisfy Actuality, their original applicative equality diagrams therefore have the same basis/common-information consequences: standard examples strictly below O, exact common information HYP, and no least solution degree. The adequate-code outputs supply the required reducts; the lower bound uses the finite-tuple convention just explained.

In particular these conclusions apply to both positive packages B and F, because B implies Actuality. They apply to additional Max/SP hypotheses only when Actuality is available; no valuation recovery is asserted for bare Max or a bare action/category presentation.

### 22.4 The positive pure-identity diagram and the maximalist one differ

For B there is an independent route using the recorded No Pure Contingency theorem. For every closed pure P, actual P is equivalent to P=top. Thus a B-model's complete actual pure theory and its closed pure identity diagram are uniformly Turing equivalent. The compiler in §22.2 can likewise test its resulting H_e proposition directly against top, without an Actuality witness.

Consequently a B-model with weak Infinity has a PA-degree closed pure identity diagram, and a standard-arithmetic B-model has a nonhyperarithmetical closed pure identity diagram computing every hyperarithmetical real. Low positive examples with Infinity still exist; they have nonstandard arithmetic.

This contrasts with Max_C: its closed pure identity diagram is the fixed C identity theory E_C of degree 0′, including in standard-arithmetic Max models. Such standard Max models have nonhyperarithmetical **actual pure theories** by §18, but their pure identity diagram remains 0′. Thus the complexity comparison depends materially on whether a code includes actual truth, and one must not transfer B's No Pure Contingency equivalence to Max.

## 23. Finite bounds force necessary lattice completeness and Relational Choice

This section applies to a consistent computably enumerable theory T extending C which is complete for closed pure sentences, including the theory C+q of a pure isolator. The independent finite-trace argument proves that every actual sort is finite and that, for every admitted sigma, T proves Box AtMost_(b_sigma)(sigma) for some effectively searchable standard bound b_sigma; see `effective-refinements.md` §§9.3–9.4. A direct structural proof of the necessary bound is also available: C proves

    Diamond AtLeast_n(sigma) → AtLeast_(n+1)((sigma t)t).          (23.1)

Indeed, n distinct sigma-objects give finite haecceity unions of each cardinality j≤n, which distinguish the Frege numerals 0,...,n. If those witnesses are merely possible, necessity of identity contrapositively transfers each possible numeral inequality to an actual inequality. Thus if the actual numerical sort (sigma t)t has exactly k objects, C implies Box AtMost_(k−1)(sigma). Nonemptiness of sigma already distinguishes zero and one, so k≥2. This proves the bound from local finiteness at the higher numerical sort; it does not assert that all accessible sorts have their actual cardinality.

The relevant schema definitions are the local records `atomicity-r.yaml`, `boolean-completeness-r.yaml`, `relational-choice-r.yaml`, and `actuality.yaml`: Bacon–Dorr, Classicism, 16 May 2023, §2.2 pp.23–25 and §2.3 pp.31–33. In C, each relational sort is already a Boolean algebra under its entailment order. The following are finite arguments in C itself, not deductions obtained by inserting T's optional assumptions into Logical Equivalence.

### 23.1 Atomicity and Boolean Completeness at a finite relational sort

For each fixed standard k≥1 and each relational sort tau, C proves

    AtMost_k(tau) → Atomicity_tau,
    AtMost_k(tau) → BooleanCompleteness_tau.                     (23.2)

For Atomicity, let p be nonzero. If no atom lies below p, every nonzero q≤p has a nonzero proper part: this is the Boolean-algebra characterization of failure of atomhood. Starting at p and repeating this finite existential step k times yields a strictly descending chain q_0>...>q_k of k+1 distinct elements, contrary to the cardinal bound. This is a fixed finite proof for each k, so it uses no induction or infinitary conjunction in the object language.

For Boolean Completeness, choose a distinct exhaustive enumeration a_1,...,a_m of the sort, with 1≤m≤k. Given any property X of tau-objects, classical case analysis on the finite list Xa_1,...,Xa_m identifies the subset S of indices where X holds at the current point. Take y to be the finite Boolean meet of the a_i for i in S, with top as the empty meet. For every z,

    (forall w (Xw→z≤w)) iff (forall i in S z≤a_i) iff z≤y.

This is exactly the recorded GLB definition. The proof uses only an externally fixed finite case split and the Boolean laws of C. It neither requires a rigid extension for X nor treats a possibly infinite property domain as externally full.

### 23.2 Actuality at a finite proposition sort

For each fixed k≥1, C proves

    AtMost_k(t) → Actuality.                                    (23.3)

Choose a distinct exhaustive enumeration p_1,...,p_m of propositions. In each finite truth-value case, let a be the meet of just the actually true p_i, with top as the empty meet. Every chosen conjunct is actually true, hence a is true by ordinary finite conjunction. If q is actually true, exhaustiveness gives q=p_i for one of the true entries, and the Boolean meet law gives a≤q. Therefore a is true and entails every actual truth, exactly the recorded Actuality formula. The case split constructs one ordinary finite term in each branch; it does not apply a truth-selection operation to arbitrary propositions or assume a truth predicate inside the language.

### 23.3 Relational Choice at a finite input sort

For each admitted sigma and tau, including tau=e, and each fixed k≥1, C proves

    AtMost_k(sigma) → RelationalChoice_(sigma,tau).              (23.4)

Let U be serial. Choose a distinct exhaustive enumeration a_1,...,a_m of sigma, then use ordinary finite existential reasoning to choose b_i of type tau with U(a_i,b_i). The admitted lambda relation

    S := lambda x^sigma y^tau .
           ((x=a_1 and y=b_1) or ... or (x=a_m and y=b_m))

is currently total and single-valued, by distinctness and exhaustiveness, and its current extension is contained in U. These are precisely Functional(S) and the unboxed subrelation clause in the recorded Relational Choice schema. Finite input tuples can be handled by the same finite enumeration of all tuples; equivalently use the recorded polyadic equivalence. Output individual objects cause no difficulty because S still has result type t.

If a formulation asks for the stronger Boolean subrelation condition S≤U, replace S by S and U, the pointwise meet. The new relation has the same current functional extension and is necessarily a subrelation of U by an unconditional Boolean identity. Thus the construction also covers that variant without a rigidity assumption.

This proof establishes a functional **relation**, not an operation sigma→tau. In particular it never constructs a forbidden individual-output type. Even for relational tau, a currently false equality mask need not be the bottom proposition without a further rigidity hypothesis, so the argument does not turn the relation into an output-valued function. No Functional Choice conclusion is inferred from (23.4).

### 23.4 Consequences for effective complete theories and pure isolators

Necessitate the genuine C theorems (23.2)–(23.4), then apply modal K to T's necessary finite bounds. It follows that every T under consideration proves:

- Box Actuality;
- Box Atomicity_tau and Box BooleanCompleteness_tau at every relational tau;
- Box RelationalChoice_(sigma,tau) for every admitted input/output pair, including individual outputs, and the corresponding polyadic schemes.

No Barcan formula is used: the proof takes a separate necessary bound and a separate genuine C finite implication at each required type. These are consequences of the complete theory T or the isolated condition q, not new theorems of bare C. They do not establish C5 or the full Functional Choice package. In particular the finite-table argument for Relational Choice must not be confused with the rigid-mask interpolation available under the positive Gallin package.

### 23.5 A fixed failure already gives the PA threshold

Fix one closed instance A among Actuality, Atomicity_tau, BooleanCompleteness_tau, and RelationalChoice_(sigma,tau). Its relevant finite-bound sort rho is respectively t, tau, tau, or sigma. The preceding C proofs show, for every standard k,

    C proves AtMost_k(rho)→A.

Consequently C+neg A proves every instance of weak Infinity at rho. Also C+neg Box A proves every possible weak-Infinity instance: contrapose the genuine C theorem, necessitate it, and apply normal modal reasoning to Diamond neg A. This second claim does not assert current infinitude of rho.

Let T be any **consistent c.e.** extension of either of those failure theories. Section 16 and `effective-refinements.md` §9.4 respectively imply that every complete pure T-theory computes binary DNR. A PA oracle conversely computes a complete witnessed extension of the fixed c.e. T, yielding an adequate countable model. Thus ordinary PA degrees are exactly the oracle capacity for complete pure T-theories and adequate T-models. The same finite-computation/recursion argument gives Sigma^0_1-complete theoremhood for every such T. These assertions are conditional on consistency; this argument does not supply a model of each proposed failure.

The completion locus S(T), when nonempty, is a compact perfect zero-dimensional metrizable space, hence homeomorphic to Cantor space. An isolated point would be the complete consequence set of a consistent finite extension T+P. That would be c.e. and complete, contradicting the DNR lower bound. Low Basis applied to each nonempty finite relative condition gives dense low completions. The usual witnessed completion algorithms also give the uniform Medvedev equivalence with the binary-DNR/PA-completion problem for the pure-theory and adequate-code conventions used earlier.

The ordinary PA oracle-capacity bounds also apply to bare original application/equality presentations by Theorem 22.2, even when Actuality fails: its nonbottom test does not recover actual valuation and does not require it. Uniform Medvedev equivalence for unnamed reduct codes is not asserted, because that proof hardcodes a finite tuple of term indices. Nor does this corollary extend to arbitrary Functional Choice failures in C: the finite-table premise established here is specifically Relational Choice.

### 23.6 A finite coalesced model shows why Functional Choice is different

Take one one-world full extensional component with a singleton individual domain, and form its full coalesced sum at a new root, with one distinguished arrow into that component. The coalesced-model theorem does not require a C-complete family of components; that additional hypothesis is needed for Max, not for validity of C. This is the recorded construction of `topics/classicism/groups/coalesced-sums.yaml`, fullest domains and distinguished arrows, based on Classicism Appendix E, Definition E.2, pp.80–83. The present finite specialization is a session example, not a new source claim.

At every relational type tau=sigma_1...sigma_m t, a root object is its arbitrary Boolean root matrix on the finite product of the root argument domains, together with one object of type tau in the component. This description includes propositions: a root proposition is a pair (root truth bit, component truth bit), so there are exactly four. Application uses partial evaluation of the root matrix and partial evaluation of the component object on transported arguments. Induction on types therefore gives finite, effectively enumerable domains and computable application at both nodes. Quantifiers and lambda terms can be evaluated on these finite domains. The model's complete actual pure theory is consequently computable.

Every type is finite at both nodes, so all the boxed lattice and Relational Choice conclusions of §23.4 hold. Nevertheless the root-only proposition r=(1,0) is distinct from bottom=(0,0) at the root and becomes bottom in the component. Thus ND_t and C5 fail at the root.

In fact even the current instance FunctionalChoice_(t,t) fails. Let

    p0=(0,0), p1=(1,0), q0=(0,0), q1=(0,1).

The inputs p0,p1 have the same component value, whereas the outputs q0,q1 have different component values. Choose a root relation U of type ttt whose actual matrix requires output q1 at input p1 and output q0 at every other input; choose its component relation to be universal. The free-root-matrix clause supplies U, and U is actually serial. But every root operation f:t→t commutes with transport to its component operation f_c. Hence

    transport(f(p0)) = f_c(0) = transport(f(p1)),

contradicting the distinct transported outputs forced by U. There is no current functional selector operation. Its current functional **graph** is nevertheless an available relation, exactly as Relational Choice requires.

Thus necessary Actuality, all-type Atomicity and Boolean Completeness, and all Relational Choice instances can coexist with a computable complete pure theory and failure of current FC_(t,t). Finite input/output domains alone do not justify the rigid-mask operation construction outside the positive package. This example also makes no claim that its complete theory is isolated by a single pure sentence; its effective completeness suffices for the stated contrast.
