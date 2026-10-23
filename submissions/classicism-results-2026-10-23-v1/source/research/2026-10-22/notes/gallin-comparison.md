# Gallin, Henkin, full semantics, and relative complexity

Research notes, 22 October 2026. Original arguments by this research agent unless explicitly attributed. No database record is changed; no Lean claim is made. The fixed types are the bundle's relational types: e, t, and sigma→tau only when tau is not e.

## 1. Exact theories and recorded evidence

Write P = C + □Plenitude = C5 + Atomicity, F = C + □Functional Choice, and M = pure Maximalist Classicism, always relative to the fixed C in Max's side condition. Let I_e denote the quantified Axiom of Infinity and Inf_e the finite-n Infinity Schema. Distinguish these throughout.

The proved-only engine confirms:

* F entails P.
* P entails □Functionality, □BF and No Pure Contingency.
* P does not entail F. Recorded witnesses include `henkin-without-relational-choice` and the explicitly choiceless full S5 variants. Their metatheoretic hypotheses must not be suppressed.
* M is incompatible with P and F; for P, already unboxed ND yields the recorded contradiction.

The relevant records are `c5-and-atomicity-imply-necessary-plenitude`, `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`, `necessary-plenitude-r-implies-atomicity-r`, `necessary-functional-choice-r-implies-necessary-plenitude-r`, and `necessary-relational-choice-and-necessary-plenitude-imply-necessary-functional-choice`. The two ordinary full Henkin records give one-world full models with one individual or countably many individuals, respectively. The second satisfies I_e; the first fails Inf_e.

Section 12 below supplies a direct ZFC finite-support Henkin separation of P from F with both quantified Infinity axioms, independent of the recorded choiceless metatheory examples. Related finite-support constructions also occur in the other research lanes.

## 2. Two meanings of a Gallin model

For this note, an extensional Gallin hierarchy has base sorts E (individuals), W (worlds), and o={0,1}, with admitted lambda terms interpreted extensionally. Translate the C types by

    e* = E,    t* = W→o,    (sigma→tau)* = sigma*→tau*.

At world w, a proposition is true iff its function has value 1 at w. Equality at every C type is genuine equality of the interpreted objects, represented as a constant world-proposition. Quantifiers range over the assigned typed domains and are evaluated pointwise. Thus Box(p), defined as p=top in C, means that p is true at every represented world.

In a **full** Gallin model every displayed function type has its entire external function set. In a **Henkin** Gallin model the domains can be proper subsets, subject to the needed lambda closure, logical operations, and extensionality. Here 'external' means in the metatheory in which the model is being considered. A hierarchy full inside a nonstandard model of set theory will generally be Henkin, not full, externally.

The forward translation into P uses lambda closure, not external fullness: a nonzero relation has a true world/argument point, whose singleton-point relation is lambda definable. Genuine equality gives C5 and these point atoms give Atomicity. If the source Gallin hierarchy additionally has its extensional selection/Choice schema, the translated model satisfies F. In ZFC, full Gallin hierarchies have such selectors because every externally chosen function is in its function domain. This forward construction is independently written in `/tmp/classicism-research/structural-world-representation.md`, §13; the parent rigidity lane is auditing reconstruction in the opposite direction.

Consequently, the full Gallin class in ZFC is too narrow to be complete for P: it validates F, while Henkin P-models can refute F. Adding the sentence ¬F_instance for a verified failed choice instance makes this a concrete counterexample. This is a semantic excess, not an inconsistency of P.

## 3. A first-order presentation and what compactness actually says

An extensional Henkin Gallin hierarchy has a routine many-sorted first-order presentation. Use a sort for each type, an application function for each arrow type, constants for the logical operations, the two Boolean truth values, and the usual truth clauses for the extensional quantifiers. Add a lambda abstraction operation for each lambda-term pattern, with its beta equations; equivalently use an appropriate typed combinatory presentation. Extensionality states that two function-sort objects with equal values at every argument are identical. Every axiom is an ordinary finitary first-order sentence. There are countably many sorts and symbols in the countable pure language.

The lambda expansion is harmless for the following argument: lambda closure with parameters is expressed by the corresponding universally quantified beta equations. These equations are preserved under elementary substructures and ultraproducts. Quantifier truth clauses have the form

    App(All_sigma,P)=1  iff  forall x:sigma, App(P,x)=1,

and so are also first-order. An elementary substructure may have fewer predicates and fewer arguments; its quantifier operation is nevertheless the correct operation relative to those smaller sorts by the displayed axiom. It need not retain external powerset fullness.

Therefore the **Henkin semantics** has compactness and downward Löwenheim–Skolem, and so does any class obtained by adding a set of first-order-translated axioms. These conclusions do not require that the added axiom set be recursively enumerable.

For general intensional Henkin semantics of C, rather than extensional Gallin semantics, use the standard applicative presentation with a truth predicate on the proposition sort. Translate every C formula A into True(value(A)); include beta/lambda and the truth clauses for logical operations, and the actual-equality clause True(eq_tau(x,y)) iff x=y. The logical constants themselves can have nontrivial intensions; this avoids imposing Gallin's rigid identity or extensional function domains. Add the translated C axioms and, if desired, the Max instances. This is again an ordinary many-sorted theory. A canonical model proof is also available syntactically by adding Henkin witnesses and quotienting closed typed terms by provable actual identity in a complete consistent extension.

In particular, **non-effective axiomatizability does not destroy compactness or Löwenheim–Skolem for M**. Given its consistency, it has a countable general intensional Henkin model. It has no Gallin model, since any model of the Gallin translation satisfies P and M is incompatible with P. One must not conflate those two claims.

Technical proviso: the general intensional presentation includes all intended term-congruence/beta laws and all C axiom translations; no claim is made here that arbitrary bare applicative structures automatically are C-models. Its use is the standard Henkin existence/elementarity construction, not a new completeness theorem for action models.

## 4. Countable positive Henkin models with genuine quantified Infinity

Take a full Gallin hierarchy in ZFC with E=N and one world. It is an F-model satisfying I_e. Expand it by the countable first-order presentation in §3 and take a countable elementary substructure. Its reduct is a countable Henkin Gallin model of F+I_e, hence of P+I_e.

Here countable means that the disjoint union of all typed domains is countable. The e-sort is infinite, since every finite lower-bound sentence follows from I_e. Its predicate sort is also countably infinite, although the external powerset of its e-sort is uncountable. Thus I_e and every internal Choice instance are preserved without preserving full powersets.

One can simultaneously require I_t by starting with W=N (and E=N if both infinities are wanted). Fullness makes the proposition sort P(W) externally infinite, and the usual impredicative finite-cardinality predicate has exactly its standard-numeral extension, so I_t holds. A countable elementary substructure preserves both quantified infinity axioms. The resulting represented-world sort is countably infinite, and its proposition sort is countable; hence it is not externally P(W).

This gives genuine I_e-models, not merely Inf_e-models which might be internally finite.

## 5. Exact cardinal growth of a full Gallin hierarchy

Assume ZFC and nonempty E,W. Put kappa=|E| and lambda=|W|. For a C relational type tau=sigma_1...sigma_n t, fullness yields the bijection

    D_tau  ≅  P(W × D_sigma_1 × ... × D_sigma_n).

The proof is repeated currying and uncurrying of a function into P(W). It uses only the actual domains at the argument types; no alternative type system is being imported. The n=0 case is D_t=P(W). Therefore

    |D_tau| = 2^(lambda · product_i |D_sigma_i|).

If either kappa or lambda is infinite, let mu=max(kappa,lambda). The cardinality of the disjoint union of all typed domains is exactly beth_omega(mu)=sup_n beth_n(mu).

Proof of the upper bound: each type is a finite syntax tree. Start with |D_e|≤mu and |D_t|=2^lambda≤beth_1(mu). If the domain and codomain of an arrow have size at most an infinite cardinal nu≥2, its full function set has size at most nu^nu≤(2^nu)^nu=2^nu. Induction bounds every type by some finite beth iterate of mu. There are countably many types, so their union has size at most beth_omega(mu).

Proof of the lower bound: if mu=kappa is infinite, start with sigma_0=e and iterate sigma_(n+1)=sigma_n t. Since W is nonempty, |D_sigma_(n+1)|≥2^|D_sigma_n|, so these sorts dominate all beth_n(kappa). If mu=lambda is infinite, D_t has size beth_1(lambda) and iteration tau_(n+1)=tau_n t supplies the remaining finite beth iterates. Their supremum is beth_omega(mu). This proves equality.

If E and W are finite, every individual type domain is finite by induction. Their countable disjoint union is countably infinite. Such a full model has a computable presentation: enumerate the finite type syntax and use finite truth tables recursively. Its sizes grow rapidly, but each computation terminates. This is not a model of either Inf_e or Inf_t.

Corollary: a full Gallin model satisfying Inf_e, I_e, Inf_t or I_t has uncountably large higher domains and no countable presentation of its entire typed hierarchy. This is a cardinal obstruction, independent of algorithmic questions about countable Henkin models. Conversely, a countable model satisfying either Infinity schema is necessarily non-full somewhere.

## 6. Explicit full-semantics noncompactness, using the bundle's Infinity definition

Let nu=(et)t and define the closed pure sentence

    Fin_e := exists Z:nu (FiniteCardinality_e(Z) and Z(top_e)),

where top_e is the universal individual property. This is the negation of the quantified Axiom I_e.

**Lemma.** In every full Gallin model, at every world, Fin_e holds iff E is externally finite.

Proof. Let z_0 denote the zero cardinality object and z_(n+1)=Suc(z_n). Let S={z_n:n∈N}, an external set of objects of sort nu. The full predicate domain D_(nu t) contains the rigid characteristic predicate of S, with value top on S and bottom elsewhere. It is an inductive predicate, so the impredicative definition of FiniteCardinality can hold only of elements of S. Conversely every inductive predicate contains each z_n by external finite induction. Thus FiniteCardinality, at every world, has exactly the set S as its extension. A separate external induction on n verifies that z_n(X) is true at w exactly when the extension of X at w has n elements. Hence z_n(top_e) is true exactly when |E|=n. This remains correct if some later numeral objects coincide when E is finite: their extensions at top_e are then false. Therefore Fin_e iff E is externally finite. QED.

Now let L_n be the pure sentence asserting at least n individuals. Every finite subset of

    Gamma = {Fin_e} ∪ {L_n:n≥1}

has a full one-world Gallin model: choose a finite individual domain at least as large as the largest mentioned n. The entire set has no full Gallin model by the lemma. Every finite model used also satisfies all of F, so adjoining F to Gamma preserves finite full satisfiability and the failure of full satisfiability.

This proves, within the precise fixed relational language:

* full Gallin consequence is not compact, even over F;
* no sound strongly complete finitary proof system can capture full Gallin consequence;
* the full Gallin class cannot be the reduct class of an ordinary first-order theory in extra sorts/symbols (such a reduct class would inherit compactness for these sentences).

Henkin compactness, in contrast, gives a Henkin F+Gamma model. Its E-domain is externally infinite while it satisfies internal Fin_e. This is the precise reason Inf_e is weaker than I_e. It does not say I_e fails in every countable Henkin model; §4 gives the opposite example.

The same noncompactness proof works at t, using full models with finite nonempty W of unbounded size: the corresponding proposition domain is finite but arbitrarily large, and the standard-numeral characterization works identically.

## 7. Full semantics carries arithmetic truth complexity

Full Gallin validity should not be described as computationally simpler than the syntactic P or F theories.

Use a variable z:e, a successor graph S:eet, and addition/multiplication graphs A,M:eeet. There is a finite second-order relational Peano sentence PA2(z,S,A,M): S is total and single-valued, injective, z is not in its range, induction holds for every e-property, and A,M obey the usual recursive equations as total single-valued graphs. Every type used is admitted in the bundle's relational hierarchy. Let phi be a first-order arithmetical sentence in relational notation. Form the closed pure C sentence

    V_phi := forall z,S,A,M (PA2(z,S,A,M) -> phi(z,S,A,M)).

**Theorem.** V_phi is valid at every point of every full Gallin model iff phi is true in the standard natural numbers.

Proof. At any world w of a full Gallin model, D_et contains a relation with every desired external subset of E as its extension at w. Therefore the second-order induction clause has full second-order meaning at w. The standard categoricity proof applies: the S-orbit of z is an available inductive subset, so it exhausts E; successor injectivity and z not being a successor identify this orbit with N; the recursion equations fix A,M as addition and multiplication. Thus if standard arithmetic satisfies phi, every local PA2 structure satisfies phi and V_phi is true. Conversely, if standard arithmetic falsifies phi, the full one-world Gallin model with E=N contains the usual successor, addition and multiplication graphs. They satisfy PA2 and falsify phi, so they refute V_phi. The map phi↦V_phi is effective. QED.

The result survives restricting the full models to those satisfying I_e: the countermodel has E=N, and the forward proof applies to every such model. It also survives requiring I_t by taking W=N and making the arithmetic relations constant across worlds. Since all these full models satisfy F, the same lower bound applies to full validity over F (and over P, which has the same full ZFC models in this sense).

Consequences: full validity is at least as hard as true first-order arithmetic, so it is not recursively enumerable and not arithmetical. More conservatively, it computes every fixed finite Turing jump. This is a lower bound, not an exact classification. The same argument can encode full second-order arithmetic truth by letting phi contain second-order quantifiers; no stronger descriptive-complexity classification is asserted here.

These statements concern standard external fullness. The finitary theorem sets of P and F remain recursively enumerable. A countable Henkin model need not have standard arithmetic and need not validate V_phi for every externally true phi.

## 8. What remains genuinely different about Max

The parent has an independent proof that no consistent recursively axiomatizable extension of C entails M. That is a sharp **effective axiomatizability** distinction from P and F. It does not establish semantic inconsistency of M, nor failure of general Henkin compactness/LS. It also does not show that full Gallin semantics is effectively simpler: §7 shows the opposite comparison if 'complexity' means validity complexity.

A safe summary is:

| Feature | P | F | M |
|---|---|---|---|
| Finitary recursive axiom enumeration | yes | yes | no consistent r.e. extension can entail it |
| General Henkin compactness/LS | yes | yes | yes, conditional on consistency for existence |
| Extensional Gallin presentation | yes, with restricted Henkin domains | yes, with internal Choice | impossible: would imply P |
| Full ZFC Gallin models | yes, but validate extra Choice | yes, but full validity exceeds effective theory | none |
| Countable Henkin models with I_e | yes | yes | yes, by the recorded coalesced root and general Henkin LS |

Do not infer a complexity ranking of individual models solely from these rows. Models, presentations, theories and validity relations are distinct objects.

## 9. Source checks and caveats

Local primary-source locators: Bacon–Dorr, *Classicism*, 16 May 2023 draft, §2.3 pp.31–33 (choice/plenitude and equivalences), §3.2 Definition 3.6 and Proposition 3.7 pp.47–48 (Henkin models), and the specific YAML records listed in §1. The externally accessible PhilPapers PDF returned HTTP 403 during this session, so no claim to a fresh direct reading of that PDF is made.

A directly read primary handout is Zachary Goodsell and Juhani Yli-Vakkuri, *Higher-Order Logic as Metaphysics*, 16 March 2021, §§6–7, PDF pp.7–9:
https://philevents.org/event/fileDownload/88518?fileId=10350
It discusses the distinction between C+□AC and ZFC-supported full interpretations, and reports a proposed comparison with a bounded-separation set theory. The latter discussion is labelled a conjecture/proof idea and works in the full simple type system. These notes do not promote it to a proved equivalence in the fixed relational fragment. The arguments in §§3–7 above are supplied independently.

For the conventional Henkin background, Leon Henkin, “Completeness in the theory of types”, *Journal of Symbolic Logic* 15 (1950), 81–91, DOI 10.2307/2266967; primary publisher record:
https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/completeness-in-the-theory-of-types1/551D2896D3C6F197030D3D8EEA911F1E
The relevant first-order presentations are written explicitly above rather than relying on an unexamined applicability of a stronger type system.

## 10. Independent audit of the world-intension transport

The parent requested an independent check of `/tmp/classicism-research/rigidity-actualization.md`, §§14–16. I read those arguments and the earlier support/actualization context. The following components pass the mathematical audit as written:

1. Atomhood is stable under C5, using BF to collect the defining quantifiers; □Atomicity/□Actuality supplies the unique true atom at every accessible point.
2. The original-argument graph G(F)(w,x)=Atom(w)∧w≤F(x) is rigid and world-supported. Its decoder J(R)(x)=∃w(R(w,x)∧w) is inverse on that supported rigid domain. The difficult direction uses a possible realization of the nonbottom atom w and uniqueness of the true atom there; rigidity of R excludes the contrary case.
3. The recursive maps j_tau and k_tau transport argument domains as well as the final world coordinate. Their existential preimages give support automatically. Inductive injectivity proves k∘j=id, and inductive surjectivity plus support proves j∘k=id. No family of choices is required: the preimages are handled inside existential formulas and uniqueness follows afterward.
4. Application preservation follows from those equations and support. This does not contradict the earlier failure of snapshot actualization to preserve application: the j-map retains all worlds.
5. The world-entailment quantifier equation is valid: w≤∀x Xx iff ∀x(w≤Xx). Forward direction is modal universal instantiation; reverse direction uses BF on ∀x□(w→Xx) followed by ordinary distribution of the x-independent antecedent w.
6. The full construction with individual and world sets N validates both original quantified Infinity axioms, and the supported rigid core is full on its base domains, so the extensional core individual/world Infinity axioms also hold.

One precision worth preserving: the target has base sorts e,s,o, but the relevant arrow types all end in Boolean o. It is not the unrestricted three-base simple-type hierarchy, and the construction has not added maps e→e or e→s to the original language. The existing translated types obey this restriction; a final theorem statement should say it explicitly.

The caution in §15 about original versus core quantified Infinity is appropriate. Formula transport directly preserves the original axiom's translated formula. It does not by itself identify that formula with a different impredicative FiniteCardinality definition over the smaller intrinsic core domains.

## 11. Max has countable Henkin models with Infinity, but requires nonstandard arithmetic somewhere reachable

### Countable models

The proved record `coalesced-maximalist-root` explicitly satisfies pure Max and the quantified Axiom of Infinity at e. Its proof is attributed to Cian Dorr (recorded 22 September 2026): root individuals are all compatible families, an infinite set; the free root component supplies a cardinality predicate picking exactly the standard numeral objects; none of these numerals counts the universal individual domain. The proved-only engine also derives the quantified Axiom at t.

Applying the general intensional Henkin downward LS argument to this model gives a **countable general Henkin model of M+I_e+I_t**. This is not a countable full action model or a Gallin model. Countability alone therefore does not separate the three theories, even after both original Infinity axioms are added.

### A qualified nonstandardness theorem

Avoid notation collision: in this subsection AI_e means the quantified Axiom of Infinity at e; J_e denotes Goodsell's I_e=◇I*_e; and I*_e is the Peano-successor condition on the Frege numbers. The recorded Goodsell result supplies PA on the numbers from J_e, hence also from I*_e by T.

Let U=C+AI_e+I*_e. This theory is recursively axiomatizable and consistent, since the ordinary full one-world model on E=N satisfies both extra axioms. Its first-order arithmetical consequences, with Frege numbers and the recorded Sum/Prod definitions, form a consistent r.e. extension of PA. By incompleteness there is an arithmetical sentence A such that both U+A and U+¬A are consistent. Therefore pure Max(C) entails both

    ◇(AI_e ∧ I*_e ∧ A),    ◇(AI_e ∧ I*_e ∧ ¬A).

This use of Max is legitimate: the two displayed matrices are closed pure C-consistent sentences. The reference theory stays C, not U. Adding I*_e explicitly avoids relying on any not-yet-audited implication from AI_e to the arithmetic hypothesis.

In any action/Kripke semantics that realizes diamonds at accessible points, choose witnesses v_0 and v_1. At both points the actual Frege number domain, with its zero, successor, Sum and Prod, satisfies PA. At least one of these domains is **not externally generated by the standard numerals**.

Proof of the last claim. If a PA structure's number domain consists exactly of the denotations 0,S0,SS0,..., PA's successor injectivity and zero-not-successor imply that n↦S^n0 is a bijection N→N_v. The recursion equations for Sum and Prod prove by external finite induction that this bijection preserves standard addition and multiplication. An induction on first-order arithmetical formulas, including quantifiers over N_v, therefore makes the structure agree with standard arithmetic. Both v_0 and v_1 cannot have this property because they disagree about A. Thus at least one accessible AI_e point has nonstandard Frege numbers. QED.

Equivalently, choose whichever of A,¬A is false in the standard natural numbers and call it B. Max(C) entails ◇(AI_e∧I*_e∧B), and every world realizing that possibility has nonstandard Frege numbers. No effective procedure deciding which side is standard-true is asserted or needed.

Scope limits:

* This is a requirement somewhere in the reachable structure of every Max model with world-realizing semantics; it is not a claim that the evaluation point is itself nonstandard.
* In fact the recorded full coalesced maximalist root can have exactly the standard Frege numbers at the root, while its components witness the contrary arithmetic possibility.
* The metatheoretic phrase “every Max model has such a reachable point” must not be rewritten as Max⊢□◇(AI_e∧I*_e∧B). Max need not hold at accessible points, so that stronger boxed conclusion has not been proved.
* The source arithmetic representation theorem is essential: merely saying that the bare set of numbers is countable or even bijective with N does not give arithmetic standardness. Numeral generation, together with the actual PA laws for Sum/Prod, is the property used.

## 12. Direct ZFC separation with both quantified infinities

This section gives a particularly simple symmetric Gallin construction. It is an independently verified specialization of the finite-support method, not a claim of literature novelty.

Let E=N, W=N, and G=Sym(W), with G acting trivially on E. Define D_t to be the finitely supported subsets of W under the natural permutation action. Equivalently, D_t is the Boolean algebra of finite and cofinite subsets of W: if A⊆W is fixed by all permutations fixing a finite support S pointwise, then membership in A is constant on W\S, giving the finite/cofinite characterization; conversely every finite or cofinite A has a finite support.

Recursively, for each admitted arrow type sigma→tau, let D_(sigma tau) consist of all finitely supported functions D_sigma→D_tau, with the conjugation action

    (g·f)(x)=g·f(g^(-1)·x).

Every entity in every domain is finitely supported by construction. Functions are actual set-theoretic functions, so application is extensional and every equality is genuine equality. At w, a proposition A∈D_t is true iff w∈A. Equality is represented by W or ∅, and the Boolean operations are ordinary set operations.

### Closure and the C axioms

All Boolean operations are equivariant. For any admitted F:D_sigma→D_t, define its universal quantification by intersection over all D_sigma. If S supports F, a permutation fixing S permutes D_sigma and preserves that intersection, so the output lies in D_t. The map F↦intersection_x F(x) is itself equivariant and therefore belongs to its prescribed function domain. Existential quantification works dually.

Lambda closure follows by induction on terms. If the parameters are supported by finite sets S_1,...,S_k, their union supports the function defined by a lambda term: a permutation fixing that union commutes with every logical operation and the recursive semantic evaluation. Bound arguments need no fixed support in this argument, because they transform with the conjugation action. Hence each denoted function belongs to the required domain. This proves the ordinary Henkin soundness conditions for H. H-equivalent matrices agree at every world and assignment, hence their lambda abstractions agree as functions; therefore C's Logical Equivalence is sound, with its original H-theoremhood restriction.

### C5 and Atomicity

Equality at every type has value W or ∅, so C5 holds. Every nonzero relation F of type sigma_1...sigma_n t has a tuple a and a world w∈F[a]. Its singleton-point subrelation

    H[b] = {w} if b=a, and ∅ otherwise

is admitted: the union of the finite supports of a_1,...,a_n and {w} supports it. It is an atom under pointwise Boolean order, and H≤F. Therefore Atomicity holds at every relational type, including t. Thus P holds.

This also directly exhibits why internal Boolean Completeness does not imply the external completeness of D_t: the finite/cofinite algebra is not externally complete when W is infinite, but the admissible higher-type families are restricted by finite support.

### The Frege numbers are externally standard, and both Infinity axioms hold

At any counting type sigma, zero and successor are pure/equivariant semantic objects, so each standard numeral z_n=Suc^n(0) is fixed by every g∈G. The external set S_sigma={z_n:n∈N} is invariant. Its rigid characteristic predicate, taking W on S_sigma and ∅ elsewhere, is therefore equivariant and admitted at type ((sigma t)t)t.

Exactly as in §6, this inductive characteristic predicate excludes every nonnumeral from FiniteCardinality_sigma, while external induction puts each z_n into every internally inductive predicate. Hence the Frege number domain is exactly the external set of standard numeral values at every world. For realized finite counts, the usual induction verifies that z_n(X) means the actual extension of X has n members.

Both E=N and D_t=FinCof(W) are externally infinite. No standard numeral counts their universal properties. Thus the quantified original Axioms AI_e and AI_t hold. Since their definitions are pure and the preceding verification is independent of the evaluation world, their boxed forms hold as well. No implication from the mere finite-n schemata is being used.

### Failure already of the (t,t) Functional Choice instance

Define a rigid relation U of input and output type t as follows. If p is the union of exactly two distinct Boolean atoms, let U(p,q) mean that q is one of those atoms; for all other p, let U(p,q) mean q=top. Equivalently, with Pair(p) meaning ∃a,b(Atom(a)∧Atom(b)∧a≠b∧p=a∨b), put

    U(p,q) := (Pair(p) ∧ Atom(q) ∧ q≤p)
              ∨ (¬Pair(p) ∧ q=top).

Atomhood, order, equality and Pair are stable, so this relation takes only W/∅ values. It is a pure equivariant function and hence belongs to D_ttt. It is serial: every two-element subset has a singleton subset in D_t, while top is the designated output otherwise.

Suppose f∈D_tt selected outputs for U at any world. Since U is rigid, for every distinct a,b∈W the value f({a,b}) would be either {a} or {b}. Let S be a finite support for f and choose distinct a,b∉S. The transposition g=(a b) fixes S pointwise, hence fixes f, and fixes {a,b}. Equivariance at this fixed input gives

    f({a,b}) = (g·f)({a,b}) = g·f({a,b}).

Neither eligible singleton is fixed by g. Contradiction. Thus Functional Choice fails at sigma=t,tau=t at every evaluation world, so □Functional Choice also fails.

The construction therefore proves, in ZFC,

    Con(P + AI_e + AI_t + ¬FunctionalChoice_(t,t)),

relative to the ordinary metatheory used to construct these sets. It is a concrete semantic separation, not merely the absence of an implication record. By downward LS, it also has a countable Henkin version preserving all those assertions. The starting construction itself need not have every type countable; finite support is not a cardinality bound on its higher function domains.

**Independent audit.** The effective-positive research agent independently checked the global equivariance of the quantifier maps, arbitrary higher-type lambda closure, the standard-numeral characteristic predicate, and the pair-selector contradiction on 22 October 2026, and found no mathematical blocker. This is an agent audit, not a named human check or a formal proof.

**Established machinery and the new application.** The finite-support method itself is classical. Andrew M. Pitts, *Alpha-Structural Recursion and Induction*, Journal of the ACM 53(3), May 2006, pp.459–506, §3.2 pp.469–471, develops conjugation actions on supported function spaces; Example 3.4 p.470 proves a choice obstruction, and Theorem 3.5 p.471 states preservation of finite support under higher-order classical constructions without Choice. Primary source checked directly: https://www.cl.cam.ac.uk/users/amp12/papers/alpsri/alpsri.pdf . That paper uses finite atom permutations; the present full-Sym(W) formulation is verified directly above. The Gallin/C5/Atomicity interpretation, both boxed Frege infinities, ordinary-core comparison, and all-type ambient-choice verdicts are the applications proved in these notes, not results attributed to Pitts.

In fact restricting the displayed action to finite permutations gives the same supported function domains. Suppose f between the already constructed full-Sym(W)-supported domains has support A for finite permutations. For any full permutation g fixing A and any x, choose a finite permutation h agreeing with g on A and on finite supports of both x and f(x); any such finite injective partial permutation extends to a finite permutation. Then hx=gx and h(fx)=g(fx), while finite-permutation support gives f(hx)=h(fx). Hence f(gx)=g(fx). Induction on types identifies the two presentations. Thus the underlying machinery is the standard nominal hierarchy, with the specific original-C interpretation and verdicts supplied here.

**Relation to existing records.** This construction is not identified with `finite-support-permutations`: that record's worlds are permutation arrows and its propositions are finitely pinned subsets of the arrow set; it is atomless and extensionally full at the evaluation object. Our worlds form the natural G-set N, our proposition algebra has singleton atoms, and our higher domains are hereditary finitely supported functions. Nor is this `full-permutation-group-infinite-set`, whose propositions are the full powerset of the permutation arrows. The recorded truncated-shift and dyadic-rounding models also have finite/cofinite proposition algebras, but their one-way transport and higher domains differ and they refute Boolean Completeness. Thus the present exact variant should be attributed to its explicit original proof here if recorded, not to an existing source's construction without a further equivalence proof. No claim of literature novelty follows from this narrow record search or the cited general nominal-set background.

### 12.1 The same model refutes every admitted ambient Functional Choice instance

The preceding separation strengthens to simultaneous failure of FunctionalChoice_(sigma,tau) for every admitted input type sigma and every admitted function-output type tau. Here tau is relational: the fixed type grammar does not admit functions returning e. In fact each negation holds at every world.

First choose a G-fixed default object d_rho at every type: d_e=0, d_t=∅, and at an arrow type use the constant bottom function. Every relational type tau also has distinct G-fixed bottom_tau and top_tau, whose flattened proposition values are constantly ∅ and W. There is an equivariant constant-proposition embedding and an equivariant evaluation projection

    c_tau:D_t→D_tau,       pi_tau:D_tau→D_t,
    pi_tau(c_tau(p))=p.

The embedding makes the flattened matrix constantly p; the projection evaluates at the chosen G-fixed default arguments. These maps have empty support and belong to the relevant domains. At tau=t both maps are the identity.

Every D_rho has infinitely many G-orbits. At e the natural-number objects are pointwise fixed. At a relational rho, c_rho maps finite world sets of different finite cardinalities into distinct orbits, since equivariance and injectivity preserve the distinction. It follows that every arrow input sigma=rho→eta has infinitely many distinct G-fixed objects: choose distinct orbits O_n in D_rho and let

    a_n(x)=top_eta if x∈O_n, and bottom_eta otherwise.

Each orbit indicator is equivariant and hence is an admitted empty-support function. Thus every input type sigma except t has an infinite G-fixed sequence (a_n)_(n≥1); at e use the natural-number objects directly. The exception t has only the two globally fixed propositions, and is handled by the pair-selector argument above.

For sigma≠t, define a rigid relation U_sigma on D_sigma×D_t as follows. At input a_n, U_sigma(a_n,p) is W exactly when p is a finite world set of cardinality n. At any input outside the displayed sequence it is W exactly when p=∅. Its value is ∅ otherwise. This is an equivariant relation, so its curried form belongs to D_(sigma)(tt). It is serial at every world, since every finite cardinality occurs among the finite world sets. The relation is an available object quantified over by Functional Choice; no claim that this particular external orbit enumeration is represented by a pure closed defining term is needed.

Suppose f:D_sigma→D_t were an admitted selector and let A⊆W be a finite support. Every a_n is G-fixed, so f(a_n) is fixed by every permutation fixing A pointwise. A finite world set with that invariance must be contained in A: if it contained a point outside A, the transitive action on W\A would force it to contain all of that infinite complement. But serial selection requires |f(a_n)|=n. Taking n>|A| is impossible. Therefore FunctionalChoice_(sigma,t) fails. The prior pair-selector proves the same conclusion for sigma=t.

Finally, for any relational output tau, pull the relevant failed rigid relation back along pi_tau:

    U_(sigma,tau)(x,y):=U_(sigma,t)(x,pi_tau(y)).

It is equivariant and serial, using c_tau to lift any available proposition witness. A supported selector f:D_sigma→D_tau would give the supported selector pi_tau∘f for U_(sigma,t), a contradiction. Because all the witnessing relations are rigid, the contradiction applies at every world. Hence the single nominal model satisfies

    P + □AI_e + □AI_t + {□¬FunctionalChoice_(sigma,tau): all admitted pairs}.

Section 17 shows that the same model also has a full ordinary e-based rigid core and therefore satisfies every translated ordinary-core Choice instance. The simultaneous failure concerns ambient selectors whose arguments and outputs may carry contingent information. It does not refute Choice inside that restricted ordinary core.

The effective-positive research agent independently audited this strengthening on 22 October 2026, including availability of the equivariant curried witnesses, the orbit-indicator construction, and the fixed-default projection argument, and found no blocker. This is an agent audit, not a human check or a formalization.

The conclusion also covers every nonempty polyadic input version: make the failed relation depend on its first input, then specialize any proposed multiargument selector at fixed defaults for all remaining inputs. A zero-input variant, if admitted as a notational edge case, is tautological and is excluded from this statement. The primary recorded Functional Choice schema has exactly the unary pair (sigma,tau) form proved above.

## 13. Two very different infinitary extensions

The user has authorized considering natural infinitary extensions. This section retains **old Max_C**, with its original finitary C theoremhood side condition. It does not silently replace C by the strengthened reference logic.

### 13.1 An external computable infinitary sentence defines Max

Work in the recursive many-sorted first-order presentation of the original finitary semantics, not inside its proposition sort. Enumerate the closed pure identity sentences as E_0,E_1,.... In this presentation each E_i can be treated as an atomic equality between denotations of closed typed terms. If helpful, add a recursively specified constant for each closed typed term and its compositional defining equations.

Let c_(i,s) be the external logical constant top if a fixed enumeration of C-proofs has displayed E_i by stage s, and bottom otherwise. The function (i,s)↦c_(i,s) is computable. Set

    Delta_Max := AND_i [ (OR_s c_(i,s)) OR NOT E_i ].

This is a computable infinitary sentence. In the conventional computable-infinitary hierarchy it has a Π^c_2 presentation: an effective conjunction of effective disjunctions of quantifier-free formulas; the displayed proof-gate inner disjunction can be merged with its extra literal. If E_i is a C-theorem its gate is true, and the clause imposes no new condition. If it is not a theorem all gate entries are false, so the clause says ¬E_i. Hence, among C-models,

    M satisfies Delta_Max iff M satisfies old Max_C.

This does not contradict the no-effective-finitary-strengthening theorem. Finitary c.e. proof search has been replaced by an infinitary formula with a countable conjunction; an effectively described infinitary syntax need not have an effective finitary complete calculus. In particular the formula can force presentations to contain 0′ even though its description is computable.

This is an **external** constraint on ordinary semantic structures. It has not introduced an entity of the original proposition sort denoting that infinite conjunction, nor lambda terms containing it, nor a new C theoremhood predicate. Those would be substantially stronger changes.

### 13.2 External standardness is also natural, but changes the degree comparison

At a fixed counting type sigma, the external infinitary sentence

    Std_sigma := forall x (N_sigma(x) -> OR_(n<omega) x=nbar_sigma)

says that every Frege number at the evaluation point is a standard numeral. It is again an effective infinitary constraint in the applicative presentation. At a Gallin point with an externally infinite counting domain, this makes the interpreted arithmetic standard; an adequate semantic presentation then computes true first-order arithmetic, not merely a PA completion. This is proved in `/tmp/classicism-research/positive-effective.md`, §11, including a direct check of the map's Sum and Prod definitions. Therefore its degree is at least 0^(omega), and in particular it is not low.

The bound is now strengthened in positive-effective §18: an adequate standard-arithmetic presentation is nonhyperarithmetical and computes every hyperarithmetical set, with a separate reduction for each set. At a standard numerical domain, the available property extensions form an omega-model of full second-order comprehension. Intersecting its available prefixed sets for Gregoriades' positive arithmetic operator produces an external fixed point, even without external powerset fullness. Gregoriades, *On a Question of Jägers*, arXiv:1905.09609v2, Theorem 1 and Lemmas 13–14, proves that each such fixed point is nonhyperarithmetical and has columns coding every hyperarithmetical set. I independently checked those source statements and the restricted-family fixed-point argument; source: https://arxiv.org/html/1905.09609v2 . This does not assert a uniform computation of Kleene's O.

This external restriction is consistent with countable positive Henkin models, even with both boxed original Infinity axioms. Start with the full Gallin structure E=W=N and take a countable elementary substructure of its auxiliary first-order presentation. The parent full structure's N_sigma is exactly the standard numeral objects at every world. If an object of the substructure satisfies the first-order-definable N_sigma at one of its worlds, elementarity says it does so in the parent, hence it is a standard numeral. Conversely every numeral is the value of a closed term and is retained by the substructure. This holds for each of the countably many original types simultaneously. The resulting countable Henkin model satisfies all the external Std_sigma constraints, while its adequate diagram is necessarily nonhyperarithmetical.

Thus “countable Henkin” does not mean “low”; imposing externally standard arithmetic removes the positive low-model examples while preserving countable positive models. The finite-support model of §12, and countable elementary submodels of it, provide a parallel standard-arithmetic P-model with failure of F.

### 13.3 Genuine countable disjunction inside lambda closure excludes old Max

Now make a different, stronger assumption: the higher-order language and semantics admit the specific countable-disjunction abstraction

    Q_sigma := lambda x^nu . OR_(n<omega) (x=nbar_sigma),

with ordinary compositional truth for the disjunction at every evaluation point. Only this computable sequence of disjuncts is needed; arbitrary noncomputable infinitary syntax is unnecessary. Q_sigma is required to denote an actual admitted property at each point, as ordinary lambda closure requires.

At every point Q_sigma contains zero and is closed under successor. Indeed if Q_sigma(x) is true, x equals some standard nbar, hence Suc(x) equals (n+1)bar and satisfies Q_sigma. The existing impredicative definition of N_sigma therefore yields N_sigma⊆Q_sigma. Conversely every nbar belongs to N_sigma by external finite induction. Thus at **every point** the Frege numbers are exactly the standard numeral values.

Apply this at sigma=e. The Max arithmetic split in §11 supplies a closed pure finitary C-consistent sentence AI_e∧I*_e∧B, where B is false in standard arithmetic. Old Max_C demands its possibility. At any world realizing that possibility, I*_e supplies the PA successor laws and the recorded Sum/Prod arithmetic interpretation, while the admitted infinitary property Q_e makes its number domain standard. B must therefore be false there. Contradiction.

Accordingly there is **no compositional world-realizing model** satisfying all of:

1. the original finitary C;
2. old Max_C;
3. the above countable-disjunction lambda closure at every point.

Equivalently, any classical infinitary calculus strong enough to express this abstraction, validate the ordinary countable-disjunction reasoning, retain the impredicative number definition, and necessitate its global logical consequences will prove the corresponding incompatibility. The semantic statement is primary; merely adjoining a weak uninterpreted infinitary symbol does not suffice.

This does not refute the original finitary Max theory. Its existing models remain models of their original framework. Nor does the argument address Maximalism redefined relative to a stronger infinitary reference logic: its old C-consistent but arithmetically false sentence need not remain consistent in the new reference logic.

Local standardness alone is also insufficient for this contradiction. The coalesced maximalist root can have standard Frege numbers at its evaluation point; §11 forces nonstandard arithmetic in some component. The obstruction is precisely to the global lambda/property closure which would make the numeral disjunction available there too.

### 13.4 A further cardinal caveat about unrestricted infinitary comprehension

If arbitrary countable disjunctions, rather than just effectively specified ones, are admitted inside lambda terms, then at a standard infinite number domain each external A⊆N determines the property lambda x. OR_(n∈A)(x=nbar). Different A give different local extensions and hence different property objects. Such unrestricted infinitary comprehension forces an uncountable property domain. Thus the countable models of §13.2, obtained merely by external standardness constraints, must not be advertised as models of unrestricted infinitary higher-order comprehension.

## 14. Full models are classified by their two base cardinalities; Henkin models are not

Here the language is pure; arbitrary named nonlogical constants would introduce additional orbit invariants. A model is pointed by a chosen actual world.

**Theorem.** Two full Gallin hierarchies on nonempty pairs (E,W) and (E',W') are isomorphic as pointed typed C structures iff |E|=|E'| and |W|=|W'|.

For sufficiency choose bijections a:E→E' and b:W→W', with b sending the actual world to the actual world. Define h_e=a and h_t(p)=b[p]. Recursively define

    h_(sigma tau)(f) = h_tau ◦ f ◦ h_sigma^(-1).

Because every arrow domain is full, this is a bijection of the corresponding typed domains. It preserves application by construction, equality by injectivity, Boolean operations by direct image on powersets, and quantifiers because each h_sigma bijectively reindexes its entire domain. Lambda interpretation is preserved by induction on terms. Pointed truth is preserved by b(actual)=actual'.

For necessity, a typed isomorphism restricts to a bijection E→E'. At t it preserves the Boolean algebra and therefore its atoms, which in the full powerset algebras are exactly the singletons. It thus induces a bijection W→W'. The unique true atom identifies the actual world, so that bijection preserves the points. Moreover every proposition is determined by its singleton atoms; hence any typed isomorphism must be the direct-image map induced by this b at t. Application then forces the displayed conjugation recursion at all higher types. Thus the pure unpointed automorphism group is exactly Sym(E)×Sym(W), and the pointed automorphisms are those with the world permutation fixing the actual world.

For finite |E|=n and |W|=k, this also gives a uniform algorithm for the complete pure theory: recursively enumerate every finite typed domain as tables and evaluate a given finite formula at the chosen world. The fact that the cardinalities grow rapidly does not prevent termination. No elementary or feasible complexity bound is asserted.

Fullness is essential. Let T be P or F together with both quantified Infinity axioms. T is consistent and c.e., and the Frege Infinity arithmetic interpretation gives an interpreted PA. The space S(T) of complete pure consistent extensions has no isolated points. For if a finite pure condition V isolated one completion, T+V would be a complete consistent c.e. theory; deciding its pure arithmetical translations would give a decidable complete consistent extension of PA, contradicting essential undecidability. The nonempty compact metrizable zero-dimensional space S(T) is therefore a Cantor space and has continuum many points.

Every such completion has a countable general Henkin model. Under P the audited representation theorem from rigidity-actualization §§14–15 presents it as a general Gallin model; under F the represented core has Choice too. Each original e-domain is countably infinite by Infinity at e. Each original t-domain is countably infinite by Infinity at t. Its atom/world set is also countably infinite: if it had only finitely many atoms, Atomicity would inject the proposition algebra into the finite powerset of those atoms. Every original relational type contains the constant relations parametrized by t, hence is also countably infinite. (The auxiliary Boolean base sort o and some auxiliary Boolean-only function sorts remain finite; the claim here is about the original C types.)

Thus there are continuum many pairwise elementarily inequivalent countable Henkin models, all with the same external cardinal pair (aleph_0,aleph_0), and indeed the same countably infinite sizes at every original type. The cardinal pair classifies full models but does not classify their Henkin counterparts. This is a precise structural meaning of the full model construction's simplicity; it coexists with the high full-validity complexity of §7.

### 14.1 Finite full Gallin points are isolated by a finite pure condition

For positive standard integers n,k, let

    V_exact(n,k) := □ND_t ∧ Exactly_n(e) ∧ Exactly_(2^k)(t),

where Exactly_m(sigma) is the usual finite sentence asserting exactly m objects of the indicated type. The bound 2^k counts propositions, not worlds. Then C+V_exact(n,k) has, up to original pointed typed isomorphism, exactly the full Gallin structure with n individuals and k worlds. Consequently its complete pure theory is an isolated point of S(C), and is uniformly computable from n,k.

Proof. The first conjunct gives C5 and hence BF and ordinary Functionality at every type. If a_1,...,a_m are the exactly-m witnesses for a sort, their distinctness is necessary by ND. Each current x equals one of the a_i, and every true such equality is necessary by NI. Therefore forall x □(OR_i x=a_i), and BF gives □forall x(OR_i x=a_i). Thus the displayed actual finite cardinalities are also necessary. This step must not be replaced by an unlicensed necessitation of an optional assumption.

The proposition domain is a finite Boolean algebra by C's Boolean equations. A Boolean algebra with exactly 2^k elements has exactly k atoms and is isomorphic to the powerset algebra of that atom set. The actual truth predicate is an ultrafilter by the classical connective truth clauses; in this finite algebra it selects a unique atom. This is the actual point.

Induct on types. Functionality makes an operation uniquely determined by its table on its finite argument domain, so its sort injects into the full finite function set. Conversely, given any finite table a_i↦b_i with relational output type tau=rho_1...rho_rt, the permitted parameterized lambda term

    lambda x z_1...z_r . OR_i ((x=a_i) AND b_i[z_1,...,z_r])

realizes that table. At x=a_i the matching mask is top and every other mask is bottom as a proposition entity, by NI/ND, so the output is literally b_i. No function type ending in e is used. Thus every arrow sort is the full set of functions between its already determined lower domains.

It remains to identify the logical operation objects, rather than merely their actual truth behavior. Equality is W or ∅ according as its inputs are equal or unequal, by C5. Boolean operations are the Boolean-algebra operations. For a quantifier on a finite sort covered by a_1,...,a_m, the boxed coverage proved above yields

    □(forall x F(x) ↔ AND_i F(a_i)).

Intensionality at t therefore identifies the universal-quantifier value with the finite meet of the table values. The existential quantifier is the corresponding finite join. Lambda denotation is forced by its beta equations and Functionality. Hence the whole original typed logical structure is the advertised full Gallin structure.

Conversely that full structure satisfies V_exact(n,k). The classification theorem identifies all choices of the point up to isomorphism. General Henkin completeness now makes C+V_exact(n,k) complete in the original pure language. Thus [V_exact(n,k)] is a singleton clopen in S(C); the finite-table evaluation algorithm computes its complete theory. QED.

### 14.2 These are exactly the isolated positive completions

The weak-Infinity theorem in positive-effective §16 now supplies the converse missing from the preceding finite-model argument. In either S(P) or S(F), the isolated complete pure theories are exactly the theories of full Gallin structures indexed by positive integer pairs (n,k).

Let B be P or F, and suppose a finite pure condition V isolates a completion Y in S(B). By completeness, Y is exactly Th(B+V). Since B is c.e., Y is c.e.; since Y is complete and consistent, racing proofs of A and not A decides Y. If Y imposed no finite upper bound on the e-domain, completeness would place every standard weak-Infinity instance asserting at least m distinct individuals into Y. The weak-Infinity theorem would then give Y PA degree, contradicting its computability. The same argument applies at t. Consequently Y proves finite upper bounds at both bases. Completeness then selects exact finite cardinalities at both; in a positive model the finite proposition algebra has size 2^k for some positive k. Section 14.1 forces the unique full Gallin(n,k) structure and hence its complete pure theory.

Conversely, section 14.1 already isolates every such theory in S(C), and full Gallin models satisfy F and hence P. These isolators therefore remain singleton clopens in both positive spaces. The pairs are distinct because finite cardinality sentences recover n and 2^k.

Equivalently, for a complete consistent pure extension Y of P or F, the following are equivalent: Y is c.e.; Y is decidable; Y is isolated in the corresponding positive completion space; Y is the complete theory of a finite-base full Gallin(n,k) structure. Indeed the weak-Infinity contradiction applies directly to any decidable Y, whether or not it was initially assumed isolated, and the finite-table identification then yields the isolator. This is a special property of these positive theories, not a general principle that decidable completions are isolated.

There is also an exact computable-presentability statement for the pure positive structures. A general model of P or F admits a computable application/equality presentation if and only if both bases are finite, equivalently if and only if it is a finite-base full Gallin(n,k) structure. The finite direction is the uniform table construction. For the converse, the Actuality witness supplied by P recovers actual valuation as p true iff a∧p=a; see sp-diagram-hat-audit §6 for the coding conditions. If either base were infinite, D_et would be infinite by the injections used in §14.3, and the weak-Infinity PA-degree lower bound at et would contradict computability. This does not require uniformly finding a from an unnamed presentation: its finite index and the conjunction index can be hardcoded in a degree argument. It assumes decidable original equality and effective application, not a quotient by merely c.e. equality or a bare action-category code.

This argument covers externally infinite Henkin models even when their Frege numbers regard a counting domain as finite: external infinitude still supplies every standard weak-Infinity sentence. The conclusion is specific to S(P) and S(F); isolated completions of C without the positive hypothesis are not classified here. Nor are the isolated points dense: the nonempty clopen positive locus of the quantified individual Infinity axiom contains none of them. This proof supersedes the earlier caution that a converse classification was unavailable.

### 14.3 The first derivative is already the perfect kernel

Let B again be P or F, and write InfSchema_sigma for the weak Infinity schema of all standard finite lower-cardinality bounds at sigma. The preceding classification gives the exact first Cantor–Bendixson derivative

    S(B)' = S(B+InfSchema_e) ∪ S(B+InfSchema_t).

Indeed a complete positive theory fails to be one of the finite-base theories exactly when it has no finite bound at at least one base; completeness then supplies the entire corresponding weak schema. Each of the two displayed loci is closed. Each is perfect: a relative finite isolator would make B+InfSchema_sigma+V a complete consistent c.e. theory containing weak Infinity, contradicting the PA-degree lower bound. Both are nonempty by full Gallin examples. Their union is therefore closed and perfect, and is a Cantor space as a nonempty compact perfect zero-dimensional metrizable space.

Thus the first derivative is already the perfect kernel. The entire positive space consists of countably many isolated finite-base theories and this kernel, but this is a set decomposition, not an assertion that the space is a topological disjoint sum. Nor does it make the isolated points dense. This formulation avoids conventions about whether the associated numerical Cantor–Bendixson rank is called zero or one.

There is a useful single-type description:

    S(B)' = S(B+InfSchema_(et)).

Constant predicates inject D_t into D_et, and identity-singleton predicates inject D_e into D_et. Conversely, if both bases are finite, Functionality injects D_et into the finite set of tables D_t^D_e. Thus D_et is externally infinite exactly when at least one of the two bases is externally infinite. These injections are direct equality/substitution arguments and use no choice principle.

The kernel is consequently an effectively closed class in the fixed sentence-bit coding: B+InfSchema_(et) is c.e. (Equivalently, exclude the computable list of finite-base isolators from S(B).) The finite-trace proof of positive-effective §16 is uniform in the chosen admitted counting type, so replacing its e or t witness sort by et gives the PA-degree lower bound uniformly throughout this kernel. The consistent c.e. Henkin presentation gives the matching PA-degree upper bound. The capacity to compute a kernel completion or an adequate model with such a completion is therefore exactly the ordinary PA-degree threshold. Low Basis applied after any consistent finite condition supplies low completions dense in the kernel. This does not give a computable completion there.

### 14.4 Every fixed ambient-choice-failure locus is perfect

Fix an admitted pair (sigma,tau). Then P+¬FunctionalChoice_(sigma,tau) entails the weak Infinity schema at sigma. For any fixed finite bound on the sigma-domain, enumerate its finitely many objects a_i, choose a witness b_i for each of the finitely many seriality instances, and combine them into one selector using the rigid equality-mask lambda of §14.1. C5 supplies the required rigid equalities and Functionality; the output remains relational. This is a finite argument for each proposed bound, with no appeal to infinite Choice. Thus failure of this choice instance rules out every standard finite input bound.

The output must also be externally infinite. Suppose instead that b_1,...,b_m enumerate D_tau, and choose an Actuality witness a. For an arbitrary serial U, put R_i(x):=(a≤U(x,b_i)). Each R_i(x) is an identity proposition, since necessary Boolean order is expressed by a∧U(x,b_i)=a. NI and ND_t make it literally top or bottom according as U(x,b_i) is actually true or false. Put B_i(x)=R_i(x)∧AND_(j<i)¬R_j(x). For relational tau=rho_1...rho_k t, the admitted lambda

    f(x)[z_1,...,z_k] := OR_i (B_i(x) ∧ b_i[z_1,...,z_k])

selects the first eligible b_i. Seriality and the finite output cover guarantee an eligible index; the disjoint Boolean masks give literal equality f(x)=b_i at that index, and hence U(x,f(x)). Only local ND_t and Actuality, besides C, were needed for this finite-output proof. Consequently P+¬FunctionalChoice_(sigma,tau) entails both InfSchema_sigma and InfSchema_tau. This assertion still concerns standard finite cardinality bounds, not quantified Frege Infinity.

Section 12.1 gives a model of this failure theory for every admitted pair. The theory is c.e. and already contains a weak Infinity schema, so its completion space has no isolated point by the PA-degree argument. Therefore

    S(P+¬FunctionalChoice_(sigma,tau))

is a nonempty clopen perfect Cantor subspace of S(P). Its completion and adequate-model oracle capacities are exactly ordinary PA degree; low completions and low adequate models exist, and low completions are dense. These conclusions require no additional quantified Frege Infinity axiom. They must not be read as proving such a quantified axiom: external or weak infinitude is the only finiteness conclusion used.

Every isolated point of S(P) satisfies F, since all finite-base full Gallin structures do. The F locus is closed, so the closure of the isolated positive points is contained in S(F). Every fixed failure locus above, and hence the open complement S(P)\S(F), lies in the perfect kernel and contains no isolated positive point. No characterization of the entire interior or boundary of S(F) is claimed.

The effective-positive agent independently audited §§14.2–14.4, including the computable-presentability classification and the finite-output argument, on 22 October 2026 and found no blocker. This is an agent audit, not a human check or formal verification.

## 15. Audit of the completion-space argument

I independently checked `/tmp/classicism-research/theory-space-comparison.md`, §§3–6, at the parent's request. No blocker was found.

* The Max locus is closed by its axiom intersection, and its nowhere-density follows from the no-consistent-c.e.-strengthening theorem applied to each finite basic condition. The relative version over an arbitrary consistent c.e. T uses T+V in exactly the same way. This is a topological category claim, not a measure/probability claim.
* The finite Gallin condition □ND_t∧Atomicity_t is justified by the specified proved records, so its locus is clopen. Adding either or both quantified Infinity axioms preserves the finite condition and consistency.
* The finite condition □ND_t∧□AtMost_n(e)∧□AtMost_m(t) really does force all of □Functional Choice. C5 supplies □Functionality, so every fixed higher sort injects into its finite application-table set. At a fixed type, finite existential choices are combined by rigid equality masks; the output type remains relational. The same finite theorem applies under the boxed base bounds at every point. No operation of forbidden type ee is introduced.
* In the nonextensional example, a full one-individual/two-world model has exactly four propositions, so the n=1,m=4 bounds are correct and the Fregean axiom fails. It is not an Infinity example.
* The hidden-variable obstruction correctly assumes an effective, complete general Henkin presentation. Its c.e. pure consequences would consistently entail Max, contradicting the metatheorem. The argument does not apply to full semantics or to the external infinitary presentation in §13.

Validation after the initial note batch: `pmap validate` completed successfully, reporting 132 principles, 447 results, 162 models. No existing database records were edited by this lane.

## 16. Exact complexity of the finite-base full family

Let K_fin be the class of full Gallin hierarchies with nonempty finite E and W. These are **finite-base** hierarchies: every fixed type domain is finite, but the union of all the countably many typed domains is not a finite structure in the ordinary one-sorted sense. The language remains the original pure finitary C language.

**Theorem.** Validity over K_fin is co-c.e.-complete (Pi^0_1-complete), and satisfiability over K_fin is c.e.-complete (Sigma^0_1-complete), under computable many-one reductions. The lower bounds already hold on the subclass with exactly one world.

The upper bounds follow from the uniform finite-table algorithm of §14: enumerate positive integer pairs (n,k), evaluate a given sentence in the unique full pointed hierarchy with those cardinalities, and halt at a false evaluation for nonvalidity or at a true evaluation for satisfiability. Arbitrarily high types are harmless for computability: a particular finite sentence uses only finitely many types and subtypes, all of whose tables can be enumerated effectively from n,k.

For hardness take a first-order sentence phi in a finite relational vocabulary R_1,...,R_m. Regard an r-ary relation symbol as a variable of admitted type e^r t and translate the first-order connectives and e-quantifiers directly. Let phi* be the result. Then

    phi is valid in all finite nonempty first-order structures
      iff forall R_1 ... R_m phi* is valid over K_fin;

    phi has a finite nonempty first-order model
      iff exists R_1 ... R_m phi* is satisfiable over K_fin.

At any world of a full hierarchy every ordinary r-ary relation on E is the local extension of an admitted variable value: use the rigid characteristic function with values W and empty. Conversely every admitted value has such an ordinary local extension. Thus universal/existential closure ranges over exactly the required finite relational structures on E. A finite counterexample or witness can already be represented with W a singleton. The first-order finite-validity and finite-satisfiability problems are respectively co-c.e.-complete and c.e.-complete, which proves the assertions.

For the external computability theorem used here, a directly checked primary source is Reijo Jaakkola, *An Extension of Trakhtenbrot's Theorem*, arXiv:2112.14996v2 (9 April 2022), §1 and Theorem 1.1, with the halting reduction developed in §3: <https://arxiv.org/html/2112.14996v2>. The passage in §1 explicitly identifies finite first-order validity as coRE-complete. The application from first-order relational sentences to this exact pure Gallin language is the argument above, not a result attributed to that paper.

Thus three different computability claims coexist: each fixed finite-base full structure has a uniformly decidable complete theory; the entire finite-base full family has co-c.e.-complete validity; unrestricted full semantics has the much higher lower bound from standard arithmetic in §7. None of these is an assertion about provability in the c.e. Henkin theories P or F.

## 17. The finite-support countermodel has a full ordinary rigid core

Use the nominal model of §12, with G=Sym(W) acting trivially on E=N. Let H be the original supported hereditary rigid core from rigidity-actualization §6, using only the original individual base e and the bivalent truth domain H_t={empty,W}. This is distinct from the expanded multi-sorted core that treats atomic worlds as an additional individual sort.

**Theorem.** H is isomorphic to the full extensional relational type hierarchy over E=N. Hence H satisfies ordinary extensional Choice and the individual Infinity axiom, although its ambient Gallin structure satisfies both boxed original Infinity axioms and refutes FunctionalChoice_(t,t).

Prove simultaneously by structural induction that each H_sigma is pointwise fixed by every element of G, and that H_(sigma tau) restricts bijectively to the full external function set (H_tau)^(H_sigma). The base claims hold because G acts trivially on E and fixes empty and W. At a general relational type rho=sigma_1...sigma_n t, an H_rho member has values empty or W and vanishes whenever an argument is outside its corresponding earlier H domain. The earlier H domains are pointwise fixed by induction. Their complements are invariant as well: if g sent an outside argument to a core member a, then g^(-1) fixes a, putting the original argument in the core. Therefore conjugation fixes the relation on every tuple, both inside and outside its support. Every core entity is consequently G-fixed.

Now let f:H_sigma→H_tau be any external function, where tau is an admitted relational output type. Define its zero extension on the entire ambient input domain by

    fhat(x) = f(x) if x belongs to H_sigma,
              bottom_tau otherwise.

Since the input core is pointwise fixed, the complement is invariant, every f(x) is G-fixed, and bottom_tau is G-fixed, fhat is equivariant. It has empty support and therefore belongs to the ambient function domain D_(sigma tau). Its values are rigid, and its expanded final-t matrix vanishes unless x belongs to H_sigma and each remaining argument belongs to the appropriate earlier core domain. Hence fhat belongs to H_(sigma tau). For tau=t the displayed default is simply the false proposition empty, so the same argument covers the base output without an extra assumption. Conversely any H_(sigma tau) member restricts to a function H_sigma→H_tau by core application closure, and its support condition determines it uniquely by that restriction. The correspondence is therefore a bijection and respects application. This completes the induction.

Under ZFC a full relational type hierarchy over N has ordinary functional and relational choice: an external choice function for a serial relation is among the full function tables (for relational outputs), and its graph is among the full relation tables. Its original individual domain is infinite, and the full predicate domains make its Frege natural numbers standard, so ordinary individual Infinity holds. These facts prove the claimed separation between core mathematics and ambient intensional choice. The ordinary extensional t-domain has exactly two elements, so no Infinity-at-t assertion is made for this one-base core.

The expanded core containing worlds does not inherit this fullness proof: G acts nontrivially on its world domain. The no-selector argument is precisely an obstruction at that additional base. Thus it would be incorrect to infer that this expanded core satisfies Choice merely because the ordinary e-based core does.

A countable elementary Henkin submodel retains every translated ordinary-core Choice instance and both boxed ambient Infinity axioms, as well as the failed ambient choice instance. It also retains externally standard Frege numbers as explained in §13.2. Its ordinary core is no longer externally full: it is a countable Henkin core over a countably infinite individual domain. Thus the theorem supplies both a full-core separation in the original large construction and a countable internally choice-satisfying core separation after downward LS. Fullness itself is not being claimed to survive elementary reduction.

There is also a **low** countable separation, obtained by a different construction. Let U consist of P, both boxed original quantified Infinity axioms, every ordinary e-core Choice instance translated through H, and not FunctionalChoice_(t,t). This is a c.e. pure theory. The H predicates are obtained by effective structural recursion on finite types; a bounded core quantifier and a core-supported lambda term have a recursive translation into the original syntax; ordinary Choice is a recursive type schema. Thus adding all its translated instances is an effective axiom enumeration. The nominal model proves U consistent.

The c.e. auxiliary Gallin presentation and Low Basis construction of positive-effective §§3–7 therefore give a countable adequate general Henkin model of U with a low presentation. Its oracle capacity is exactly the ordinary PA-degree threshold established there for consistent c.e. packages with Infinity: the weak Infinity schema supplies the lower bound, and the consistent c.e. presentation supplies the upper bound. This applies to computing some model of U, not to the degree spectrum of a fixed isomorphism type. Such a low model has nonstandard Frege arithmetic: externally standard Frege numbers would force its adequate presentation to be nonhyperarithmetical by positive-effective §18 (already the earlier true-arithmetic bound excludes low presentations). It is **not** a low elementary submodel of the original standard-numeral nominal model. The elementary-submodel construction and the Low Basis construction preserve different additional properties.

The stronger separation in §12.1 permits replacing the single failed instance in U by the entire recursive schema {□¬FunctionalChoice_(sigma,tau): all admitted pairs}. The strengthened theory remains c.e. and is consistent in the same nominal model. Thus the low countable separation, the exact PA-degree capacity, and the nonstandard-arithmetic conclusion all hold while every ambient Functional Choice instance fails at every world and every ordinary e-core Choice instance holds.

The effective-positive agent independently audited §§16–17 on 22 October 2026 and confirmed the finite-validity reduction and the pointwise-fixed/zero-extension proof. This is an agent audit, not a named human check or a formal proof.

## 18. Audit of the later Infinity-transfer results

An independent audit of rigidity-actualization §§17–19 found no blocker. In §17, the pullback of core inductive predicates gives h(N) contained in Nc, and the actualized image predicate gives the reverse inclusion without external standardness or any choice principle. The actual BE evaluator is used locally to recognize the image, while the output's bivalence and support give membership in the rigid core. Injectivity of h is not assumed at this stage.

In §18, Frege-finiteness and adjunction-finiteness are equivalent by internal impredicative induction. The resulting proofs that subsets, functional images and available power domains of finite predicates are finite require only available comprehension, so they apply to Henkin domains and internally nonstandard finite sets. The atomic-world graph bijection then transports the precise original quantified Infinity_t axiom to Infinity of the atomic-world sort. This does not assert external powerset fullness.

In §19, the explicit world lift L preserves zero and successor, and hL is the identity on core cardinalities. The original induction predicate Lh(Y)=Y consequently contains all original natural cardinalities. Combined with §17's surjectivity, this gives the stated inverse isomorphism. Its proof uses Atomicity and the represented true atom; those stronger hypotheses correctly enter only here. The earlier all-propositions core and the atomic-world core remain distinct throughout.

## 19. External standardness transfers between counting bases

This section refines the canonical numerical graph of frege-infinity-20261022-1726 §13. Distinguish external numeral coverage StdCov_sigma, which says every current N_sigma-object equals a standard numeral value, from external Peano standardness StdPeano_sigma, which additionally says those numeral values are pairwise distinct. Neither is an extra finitary sentence of the original language. Statements below first concern the evaluation point; their modal scope is stated separately.

For counting types rho and sigma, let J(n,m) be the intersection of all relations containing (0_rho,0_sigma) and closed under simultaneous successor:

    J(n,m) := forall Q [ (Q(0_rho,0_sigma) and
      forall u,v (Q(u,v) -> Q(Suc_rho u,Suc_sigma v))) -> Q(n,m) ].

**One-sided graph theorem.** C+I*_rho proves that J is a total single-valued successor-preserving surjection from N_rho onto N_sigma. No I*_sigma, Plenitude or Choice hypothesis is needed. If I*_sigma also holds, it is a bijection.

Here are the points at which the hypotheses enter. The conjunction N_rho(n) and N_sigma(m) is an inductive relation, so J is contained in that product. The definition gives the base pair, successor closure and induction for available relations. It also gives decomposition: each J-pair is either the base pair or a simultaneous successor of a J-pair. Indeed the displayed decomposition property contains the base and is successor-closed, since each pair satisfying it already belongs to J. Induction on N_rho applied to the property of having a J-mate proves totality on the first coordinate. Symmetric induction on N_sigma proves totality on the second coordinate; neither totality argument uses an I* hypothesis.

For single-valuedness, induct on n in N_rho. At zero, decomposition and zero-not-successor at rho force the mate to be zero_sigma. At n=Suc_rho(u), decomposition expresses two possible mates as Suc_sigma(v), Suc_sigma(v'), with J(u',v), J(u'',v') and Suc_rho(u')=Suc_rho(u)=Suc_rho(u''). Successor injectivity at rho gives u'=u=u'', and the induction hypothesis gives v=v'. Target successor congruence gives equality of the mates. No injectivity at sigma was used. Reversing coordinates under I*_sigma proves injectivity. All statements use relational graphs at admitted types, never an individual-valued function type.

It follows that, in any C-model satisfying I*_rho and StdPeano_rho at its current point, StdCov_sigma holds for every counting type sigma. Given a target number m, surjectivity supplies a source n. Source standardness identifies n with a standard numeral nbar_rho; finite successor closure gives J(nbar_rho,nbar_sigma), and functionality identifies m with nbar_sigma. If the target also satisfies I*_sigma, its numerals are distinct, yielding StdPeano_sigma. Thus under both I* hypotheses, external Peano standardness at rho and sigma is equivalent.

There is a stronger useful target condition. If InfSchema_sigma holds, each fixed finite numeral has the ordinary finite-cardinality extension, standard finite witness properties separate all its numeral values, and no numeral counts the universal sigma-property. Combined with StdCov_sigma, this gives both StdPeano_sigma and the original quantified AI_sigma. Consequently a single externally standard Peano counting base transfers standardness and quantified Infinity to every externally infinite counting sort. This is a semantic conclusion using the entire weak Infinity schema; it does not prove AI_sigma from that schema alone without the source-standardness condition.

**All-world scope under P.** In general Gallin models of P, all original domains and equality are fixed across the represented worlds. The C theorem N_sigma(n)→□N_sigma(n), together with S5, makes membership in N_sigma constant across those worlds; the pure numeral objects themselves are fixed as well. Hence actual StdCov_sigma or StdPeano_sigma holds at every represented world. The preceding pointwise transfers therefore give global standardness under P, with the same explicit arithmetic or weak-Infinity hypotheses. Actual AI_sigma implies I*_sigma already in C; boxing an optional hypothesis is not part of the argument.

In particular, P+AI_e+AI_t together with external StdPeano_e has externally standard Frege numbers and the quantified AI_sigma at every world for every original admitted sigma. Both bases are externally infinite. Every relational domain contains an injective constant-proposition copy of D_t, so every admitted sort is externally infinite; apply the previous transfer and world-invariance arguments. Both original boxed base Infinity axioms follow as well. Without P this last world-invariance step is unavailable: the standard-root Max construction can have externally standard actual Frege arithmetic while Max forces reachable arithmetic points with nonstandard numbers. Current-point standardness and standardness at all accessible worlds must remain distinct.

The effective-positive agent independently audited the one-sided graph proof, the weaker target weak-Infinity condition, and the need to distinguish current-point from global standardness on 22 October 2026. The graph proof is an original refinement of the source note's two-sided theorem, not a theorem attributed to an external paper.

## 20. Finite worlds separate truth-type choice from higher-type choice

There is a useful variant of §12, suggested by the effective-positive agent. Let E=N carry the natural action of G=Sym(E), let W={0,1} carry the trivial action, put D_t=P(W), and recursively take all finitely supported functions at admitted arrow types. The quantifier and lambda-closure arguments of §12 apply unchanged: each quantifier map is equivariant, its output belongs to the full finite proposition domain, and the union of the finite parameter supports supports a lambda denotation. Equality is literal identity, represented by W or the empty set, so C5 holds.

For Atomicity, any nonzero relation has a tuple a and a world w in its value there. The relation taking the singleton {w} exactly at tuple a and the empty proposition elsewhere is supported by the union of the finite supports of the tuple entries. It is an atom below the original relation. Thus the model satisfies P. The pure numeral objects are G-fixed, and the external set of standard numeral values has an admitted invariant characteristic predicate, so every Frege number is a standard numeral value. At e, the infinite individual domain separates the numeral values and none counts the universal property; hence □AI_e and externally standard Peano numbers hold. AI_t is false because D_t has four elements. Two worlds make this a non-Fregean positive model.

Every type built from t alone is finite, pointwise G-fixed, and has its full function tables: this follows inductively from the finite full proposition base, since every map between two such finite fixed domains is equivariant. The finite-input and finite-output interpolation arguments of §14.4 therefore prove every FunctionalChoice_(pi,tau) and every FunctionalChoice_(sigma,pi), at every world, whenever pi is built only from t. In particular this covers t itself. In fact every FunctionalChoice_(e,tau) holds as well. Fix a world w and a serial relation R with finite individual support S. Choose a_0 outside S and a witness b_0 with w in R(a_0,b_0). Let B be a finite set containing S, a_0 and a support for b_0. For a outside B, define f(a)=(a_0 a)·b_0, where (a_0 a) is the transposition. It fixes S, hence R, and sends a_0 to a; since worlds have trivial action, w belongs to R(a,f(a)). For each of the finitely many a in B choose an eligible b_a and set f(a)=b_a.

The function f is finitely supported. Enlarge B to A by adjoining the finite supports of all the exceptional witnesses b_a. A permutation g fixing A fixes each input in B and each b_a. On the complement of B, conjugation gives g·((a_0 a)·b_0)=(a_0 g(a))·b_0, because g fixes a_0 and b_0. Thus f(g(a))=g·f(a) on both pieces. Therefore f belongs to D_(e tau) and witnesses the required choice instance at w. The proof is independent of w, so the instances are necessary. This argument uses finitely many external choices only; it assumes no ambient infinite Choice axiom.

Every finite nonempty tuple of e-inputs also admits choice, by induction using these unary instances. For example, first choose, for each x, an operation h of type e→tau selecting the y-fibers; then apply FunctionalChoice_(e,e tau) to select such an h for each x. Currying gives the desired binary selector. All output types used in this induction are admitted relational types. Finite t-inputs can likewise be added using finite interpolation.

Nevertheless FunctionalChoice_(et,et) fails at every world. For each two-element subset {a,b} of E, let P_{a,b} be its rigid characteristic e-property, taking W on {a,b} and the empty proposition elsewhere. Define a rigid relation U(F,H) that, at such a P_{a,b}, requires H to be P_a or P_b; at any other input it requires H to be the empty e-property. This relation is equivariant, hence admitted, and serial.

Suppose a selector f had finite individual support A. Choose distinct a,b outside A. Their transposition fixes A and P_{a,b}, and therefore fixes f(P_{a,b}); yet it exchanges the only two eligible outputs P_a and P_b. Contradiction. This proves the simultaneous separation

    P + □AI_e + {□FC_(e,tau), □FC_(t,tau), □FC_(sigma,t): all admitted sigma,tau}
      + □¬FC_(et,et).

Replacing W by a singleton gives the corresponding extensional/Fregean Henkin model without Choice. The version with two worlds isolates a different phenomenon from §12: all truth-input and truth-output instances hold, while a higher-type instance fails. Its ordinary e-core does not have §17's fullness property, because G now acts nontrivially on E. No claim that ordinary e-core Choice holds in this variant is made.

This is another application of the standard nominal machinery cited in §12. It proves that all instances with basic input e or t, even together with every instance with output t, do not suffice for full Functional Choice. It does not prove a strict hierarchy at every type level or failure of finite relative axiomatizability.

The effective-positive agent independently audited this variant, including the unary e-input selector and its finite-tuple extension, on 22 October 2026. The source, scope and verdict distinctions from the moving-worlds model in §12 are essential.

### 20.1 External countability, internal amorphousness and Dedekind-finiteness

The same model has E=N externally, yet no admitted relation numerically codes all its individuals. This is an internal/external distinction, not an external uncountability assertion. The proofs below hold at each of the two worlds.

First, every admitted individual property X:E→D_t has finite or cofinite current extension. If A supports X, the subgroup fixing A acts transitively on E\A and trivially on W. Thus X has one proposition value outside A. At a fixed world its extension either contains all of E\A or none of it. All finite individual properties occur, by finite equality disjunctions. Since N_e is externally standard and its numerals have their ordinary finite extensions, current Frege-finiteness of an individual property is equivalent to external finiteness of its extension. Therefore E is internally amorphous in the exact sense that it is Frege-infinite and every available property X or its complement is Frege-finite. In particular it has no available partition into two Frege-infinite parts.

For any counting base rho, use the admitted individual-domain version of the numerical graph-code formula:

    Ctbl_(rho,e)(E) := exists R^(e nu_rho t) forall x,y^e .
      [ (exists n in N_rho . R(x,n) and R(y,n)) iff x=y ].

This is the same code-sharing definition as the recorded Ctbl formula, now with individual input; every type displayed is admitted. No such R exists. Let A support a proposed R and choose distinct x,y outside A. The case x=x gives a number n with R(x,n). Every member of N_rho is a standard numeral value and is G-fixed, including at finite counting bases where those values can collapse. The transposition of x and y fixes A, n and the evaluation world, so R(y,n) holds as well. Their shared code contradicts x≠y. Thus numerical countability of E fails for every counting base rho, even though E is externally countably infinite. No least-code principle or choice conversion was used.

The individual domain is also relationally Dedekind-finite: every admitted relation R⊆E×E that is currently the graph of a total injective self-map is currently surjective. To prove this, let A support R, and let f denote its external actual function. Single-valuedness makes f equivariant under the subgroup G_A. For x outside A, any permutation fixing A and x fixes f(x), so f(x) belongs to A∪{x}. If f(x) belonged to A, equivariance and transitivity of G_A on E\A would give the same output at every input outside A, contradicting injectivity. Hence f(x)=x outside A. For x in A, G_A fixes x and consequently fixes f(x), so f(x) belongs to A. The injective restriction A→A is a permutation. Thus f is surjective on E. This proof concerns an admitted graph of type eet; it does not posit a forbidden function object of type e→e.

Finally there is no admitted total injective graph N_e→E. If A supports such a graph, every number input is G-fixed, so its unique output is fixed by G_A and therefore belongs to the finite set A. The infinitely many distinct standard e-numerals cannot inject into A. This gives a direct obstruction to selecting a sequence of distinct individuals, even though every unary e-input Functional Choice instance, with arbitrary admitted relational output, holds.

All these assertions are world-independent in this model. Their pure graph and quantified-finiteness formulations therefore hold necessarily. The model thus separates quantified individual Infinity from relational Dedekind-infinitude and numerical countability, while retaining standard numerical arithmetic and the entire individual-input Functional Choice fragment. The effective-positive agent independently audited the support arguments on 22 October 2026.

## 21. The finite-axiomatizability question for full Functional Choice remains separate

P has the finite relative axiom V_G discussed in §15, while F is presented by the recursive all-type boxed Functional Choice schema. A schema presentation alone does not settle whether an equivalent finite relative axiom exists. The narrow local search and the checked author-hosted Classicism draft (1 July 2022), §2.3 printed pp.31–33, supply the equivalence of Functional Choice with Relational Choice plus Plenitude and a Henkin consistency route for failure of Relational Choice. They do not establish finite axiomatizability or its failure for F in this fixed type grammar. No claim about the state of the wider literature follows from this search.

By compactness, non-finite relative axiomatizability would follow from this precise construction task: for every finite collection Delta of boxed Functional Choice instances, produce a C-model satisfying Delta but failing some boxed Functional Choice instance. Indeed, if F had a finite relative axiomatization V, the derivation of V from F would use only finitely many of its schema axioms. Conversely, a finite schema package entailing every instance would itself be a finite relative axiomatization. The proofs of §§12 and 20 do not furnish the required family: §12 fails all instances simultaneously, and §20 separates a large truth-type subfamily from higher-type Choice without handling arbitrary finite packages. This question is therefore left unresolved here.

### 21.1 A primary-source lead with an unresolved interpretation problem

A later targeted search located Mitsuru Yasuhara, “The axiom of choice in Church's type theory. Preliminary report,” Notices of the American Mathematical Society 22 (January 1975), p.A-34, abstract 720-02-8, Theorem 2. The indexed text of the primary AMS issue was inspected at https://www.ams.org/journals/notices/197501/197501FullIssue.pdf ; direct PDF opening returned 403. The announcement describes models with precisely prescribed upward-closed failures of type-indexed Choice, where the printed order is generated by immediate component types. This is a promising lead, not a checked construction or an established transfer to our F schema.

There is a concrete reason for caution. If AC_alpha means existence of some global selection function on nonempty alpha-properties, such choice transfers along every definable retraction beta→alpha→beta. Let i and r satisfy r(i(x))=x. Given a beta-property P, form its i-image at alpha, choose an element of that image, and apply r. This defines a beta-selection operation whenever the alpha-selector exists.

Already within the original admitted relational grammar, take beta=e→t and alpha=e→(t→t), with

    i(f)=lambda x^e p^t . f(x),
    r(g)=lambda x^e . g(x)(top).

Extensional type theory proves r(i(f))=f. Yet beta is not a syntactic component subtree of alpha. Consequently the printed theorem, interpreted simultaneously as a classification of existential-selector failure and as the plain syntactic component order, would permit a model with an alpha-selector but no beta-selector, contradicting this retraction. The original announcement does not spell out the formula denoted by AC_alpha. In particular failure of a specified description/selection constant to select is not automatically failure of existence of every selector. A missing convention about the type order would also matter. The current search has not resolved this interpretive issue.

Peter B. Andrews, “General models, descriptions, and choice in type theory,” Journal of Symbolic Logic 37(2) (June 1972), pp.385–394, doi:10.2307/2272981, is the paper to whose Theorem 4 the announcement refers. Its publisher-hosted extract confirms that its initial language has equality and extensionality but no description or selection operator; that extract alone does not identify Yasuhara's later convention or prove the claimed hierarchy. Accordingly no non-finite-axiomatizability conclusion is drawn from the announcement in these notes, and the caveat in §21 remains in force.

### 21.2 One global-selector assertion packages each output type

For each relational output type tau, define the original pure sentence

    Sel_tau := exists epsilon^((tau t) tau) forall P^(tau t) .
                 ((exists y^tau . P(y)) -> P(epsilon(P))).

This asserts existence of some selector operation, not selection by a previously designated constant. C proves that Sel_tau is equivalent to FunctionalChoice_(tau t,tau), and proves Sel_tau→FunctionalChoice_(sigma,tau) for every admitted sigma. Thus the entire input-type schema at fixed output tau reduces to one instance.

For the forward construction from FunctionalChoice_(tau t,tau), use the serial relation

    U(P,y) := ((exists z . P(z)) -> P(y)).

Its seriality is a pure logical theorem: if P has a member use one; if it does not, every y works, and the type is nonempty. Functional Choice supplies precisely the epsilon in Sel_tau. Conversely, given epsilon and any serial R of type sigma tau t, define

    f := lambda x^sigma . epsilon(lambda y^tau . R(x,y)).

Seriality makes the displayed y-property nonempty, so the selector clause yields R(x,f(x)). Only lambda existence and beta conversion are used. All types end in the permitted relational output tau. Taking sigma=tau t gives the converse implication to the distinguished choice instance.

These are discharged C theorems. Necessitation and modal K give their boxed counterparts without necessitating an optional assumption. Consequently

    F = C + {Box Sel_tau : tau an admitted relational output type}.

The remaining finite-basis question is therefore an output-type question. This reduction does not show that finitely many output types suffice, or that they cannot suffice.

### 21.3 Single-axiom strict intermediate packages

Put T_tt:=C+□FunctionalChoice_(t,t), and put G:=C+□Sel_t. Then, as theories in the original fixed framework,

    P is strictly weaker than T_tt, which is contained in G,
      and G is strictly weaker than F.

Both T_tt and G are single-axiom extensions of C and strict intermediate theories between P and F. No separation or equivalence between T_tt and G has been established here. The input type of the G axiom's equivalent choice instance is tt, whereas T_tt uses input t. The letter H is avoided because it already names the standing pre-Classicism proof system.

Already T_tt implies P. FunctionalChoice_(t,t) gives the same Plenitude instance. For current distinct propositions x,y, the functional relation sending x to top and every other argument to bottom yields an operation f with f(x)=top and f(y)=bottom. NI preserves these identities; possible identity of x,y would then identify top and bottom. Thus this Plenitude instance implies ND_t. Necessitating the discharged C implication yields □ND_t from T_tt. The proved record `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` lifts this to all of C5.

The recorded Plenitude→Actuality proof likewise uses only input t and output t: represent the functional relation sending a true p to p and a false p to top, then take the conjunction forall p f(p). It is true and entails every true proposition. Thus T_tt gives □Actuality. The proved record `c5-and-necessary-actuality-imply-atomicity`, Classicism Proposition 2.6, pp.25–26 in the 16 May 2023 draft, then gives all-type Atomicity. C5+Atomicity is P. The exact-instance Plenitude proofs are `plenitude-r-implies-distinctness-necessary-r` and `plenitude-r-implies-actuality`, Classicism Propositions 2.13 and 2.15, pp.32–33. Every box in this argument comes from a discharged C implication, not from necessitation under an optional hypothesis.

Section 21.2 proves G→T_tt and F→G. For strictness, the moving-worlds model of §12.1 satisfies P and refutes FunctionalChoice_(t,t), so it refutes T_tt and G. Conversely, the moving-individuals/fixed-two-worlds model of §20 satisfies □Sel_t because its proposition domain is finite, but it refutes FunctionalChoice_(et,et), so it refutes F. These are concrete model separations, not absent-record inferences. The second separating model has □AI_e and externally standard N_e; no AI_t is claimed there because its proposition domain is finite.

**Consolidation audit.** The parent and effective-positive agents independently checked §§21.2–21.3. A final adversarial audit of comparison-handoff-20261022 §§5–7 preserved the following boundaries: unary ambient Choice excludes forbidden individual outputs and nullary tautologies; the fixed-world variant has only individual quantified Infinity, whereas the moving-world variant has both base infinities; countable elementary submodels of the standard construction and low nonstandard models are different constructions; current-point standardness transfers in C require the stated I* or weak-Infinity conditions, while all-world transfer uses P; all higher possibility stages remain explicitly consistency-conditional; ordinary relative distinctness maximalization is idempotent and differs from the optional hat hierarchy; the two strict intermediate packages do not settle finite relative axiomatizability of F. No effective homeomorphism to Cantor space, human check, Lean verification, or new database verdict is asserted.
