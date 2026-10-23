# Hostile audit: standard Frege arithmetic and presentation complexity

22 October 2026. Independent ordinary mathematical audit of `positive-effective.md` §§18–19 by the parent audit agent. No human check, Lean status, main-database edit, or novelty claim. Primary computability sources were opened directly during this audit. The parallel Gallin auditor is separately checking the presentation distinctions.

## Verdict

**PASS, with the stated scope retained.** The standard-number lower bound, the explicit Π⁰₂ class of standard Henkin codes, the below-O examples, the common-HYP theorem and the no-least-degree conclusions follow. No unsupported passage from finite jumps to all hyperarithmetical sets is needed: the fixed positive arithmetic operator supplies the missing strength. The proofs concern actual external standardness, not a finitary axiom that ensures it. The positive-model construction establishes no consistency or standard-number model for Strong Possibility.

## 1. The interpretation really is an omega-model of full comprehension

Fix a counting type σ. The exact arithmetic premises are I_σ and Std_σ at the evaluation point. I_σ gives the recorded PA interpretation. External standardness makes its zero/successor and, by finite recursion, its addition/multiplication standard on every numerical tuple.

Let S be the actual numerical extensions of available predicates X:νt, where ν=(σt)t. Quantification over original predicate entities covers S, possibly with repeated extensions. Translate second-order set equality by coextension on the numerical domain, not original intensional identity. Then all translated formulas are invariant under replacement of a set parameter by another intension with the same extension. An induction on formulas therefore gives the exact second-order satisfaction interpretation.

For every second-order formula φ(n,X̄), the original term λn(Nn∧φ#) has its requested extension. Set quantifiers cause no obstruction: they are ordinary admitted quantifiers over the type νt. Numerical induction is externally true on standard N. Thus the resulting structure is an omega-model of full second-order comprehension. No full external powerset and no higher-order Choice have been used.

Weak Infinity plus Std_σ is a sufficient alternative route to I_σ: no standard finite numeral counts an externally infinite counting domain, giving the quantified Infinity axiom and its recorded arithmetic consequence. The proof does not silently replace weak Infinity with its stronger quantified form absent the standardness assumption.

## 2. The fixed-point argument is sound in a restricted Henkin set domain

Gregoriades supplies a particular positive arithmetic operator Φ with no hyperarithmetical fixed point. In the interpreted omega-model, arithmetic comprehension gives Φ(X)∈S for X∈S. Standard arithmetic makes this the same external arithmetic operation, and positivity gives external monotonicity.

Full comprehension gives the set

    L={n: for every X∈S, Φ(X)⊆X implies n∈X}.

The family of available prefixed sets is nonempty (N itself is prefixed). For each such X, L⊆X and hence Φ(L)⊆Φ(X)⊆X. Therefore Φ(L)⊆L. Monotonicity now makes Φ(L) an available prefixed set. Using it in the defining intersection gives L⊆Φ(L). Thus L is an external fixed point.

This does not assert that S is externally complete or that L is the external least fixed point. Neither assertion is needed. The source obstruction concerns every fixed point. The displayed definition is one fixed pure original term after inserting the pure N, Sum and Prod definitions; model-specific set parameters have not entered it.

The source's column lemmas give more than nonhyperarithmeticality: each hyperarithmetical set occurs as a standard numbered column of any such fixed point. The reduction may hard-code that column number. This is an individual reduction for each set, with no effective enumeration of valid ordinal notations. It follows that the complete actual pure theory computes L and every hyperarithmetical set, but it does not follow that it computes Kleene's O.

## 3. Exact coding obligations

For a complete actual pure theory Γ, query its bit for the closed sentence L(numeral n). This uniformly computes L. An adequate original code with parameterized term interpretation and actual truth uniformly computes Γ and therefore has the same lower bound. No semantic truth predicate is presumed within C.

For an **auxiliary atomic diagram**, the separate reduction is valid. In a fixed presented H0/Hch model, hard-code the finitely many element indices naming the denotations of zero, successor, L, the selected world, and Boolean 1. Successive application computes the nth numeral; application of L and then evaluation at that world computes its membership bit. Application and equality are part of that auxiliary atomic presentation. The hard-coded tuple need not be uniformly discoverable from an unnamed atomic diagram; the claim is a Turing-degree lower bound for each presentation. Naming finitely many existing elements changes no such degree.

This argument must not be generalized to a reduct that omits the relevant auxiliary types/application, or to an arbitrary category/action code. It also does not show that an atomic diagram uniformly computes the full elementary diagram. Only the particular fixed-point set is extracted by these finitely many represented operations.

## 4. The standard-code class has the claimed effective complexity

Use the specified c.e. Hch theory with its positive cardinality/Infinity requirements, the finite definitional expansions, and a fixed c.e. Henkin expansion. A complete consistent characteristic theory D is described by Π⁰₁ conditions: all failure witnesses are finite proof or coherence configurations.

For every numerical closed term u impose

    D(N(u)(w0)=1)=1 ⇒ ∃n D(u=Suc^n(0))=1.

The quantification over u,n is over ordinary term codes and natural numbers. Each displayed D query is a single bit. Hence this is Π⁰₂. Requiring it at every closed world term, or at finitely many counting types, remains Π⁰₂. Strong Infinity guarantees that the numeral values are distinct. Since every term-model entity has a closed name, the condition is exactly external standardness of the numerical extension at the requested points.

Nonemptiness is justified independently of effectiveness. The full hierarchy over E=N and the specified finite/infinite world set satisfies Hch and has standard number fields. Interpret fresh Henkin constants by actual witnesses. Its expanded complete theory meets the syntactic conditions; the corresponding countable term model is standard by the displayed condition. For the two-world package, standardness is imposed at the infinite e-counting domain; it must not be required at the finite t-domain. The infinite-world package permits both e and t.

Thus K is a nonempty lightface Π⁰₂, and therefore lightface analytic, class. The ordinary effective Henkin constructions compute the stated diagrams/model codes/pure theories from D. Their transformations do not require a further jump. These are specified output presentations, not claims that all possible presentations are computable from the same D.

## 5. The basis-theorem applications preserve their hypotheses

The checked Gandy/Kleene basis result supplies D∈K recursive in O, with O not hyperarithmetical in D and ω₁^D=ω₁^CK. Each output Q is Turing reducible to D. Section 2 makes Q nonhyperarithmetical. If O≤TQ, then O would be hyperarithmetical in D, contradiction. Consequently Q<T O, O is not hyperarithmetical in Q, and ω₁^Q=ω₁^CK by monotonicity of the relative admissible ordinal.

For a nonhyperarithmetical X, the checked Kreisel basis consequence supplies some D∈K such that X is not hyperarithmetical in D. Its output Q cannot compute X (and cannot even make X hyperarithmetical). Thus, over the stated positive solution classes, the sets common by Turing reduction to **every** solution are exactly HYP. The same argument works with hyperarithmetical reducibility in place of Turing reducibility. The source's countable-avoidance theorem justifies the simultaneous version for any countable list of nonhyperarithmetical sets.

The stronger Hch witnesses suffice for the upper/avoidance direction for the weaker H0, B or C packages. The lower direction applies to every standard-number solution independently. This combination is legitimate; it would not establish the same avoidance result for an arbitrary strengthened theory without a nonempty appropriate analytic witness class.

No least solution Turing degree or hyperdegree follows by contradiction: a representative of a least solution degree would be common to all solutions, hence hyperarithmetical, contradicting their lower bound. For the upward class of oracle degrees computing some solution, a least member would compute a solution whose degree is itself capable and no larger; leastness would make those degrees equal. Therefore that oracle class also has no least degree. This is **no least**, not a claim of no minimal elements or an exact classification of every solution degree.

## 6. Primary-source check and boundaries

Directly inspected sources:

* Vassilios Gregoriades, [On a Question of Jägers](https://arxiv.org/pdf/1905.09609), arXiv v2: Theorem 1, printed pp.2–3, and Lemmas 13–14, printed pp.7–8. These support respectively the nonhyperarithmetical fixed-point obstruction and the column property used here.
* Leo Harrington, Richard A. Shore and Theodore A. Slaman, [Σ¹₁ in every real in a Σ¹₁ class of reals is Σ¹₁](https://math.berkeley.edu/~slaman/papers/Sigma1116.pdf), draft dated 11 July 2016: Theorem 2.1 and its Kreisel explanation, printed p.2; countable avoidance Theorem 2.6, p.6; and Gandy/Kleene Theorem 2.9, p.7. The latter explicitly includes recursiveness in O together with strictly smaller hyperdegree.

The imported statements match the draft's use. All reductions and the construction of K were checked separately above. No standard-SP model or consistency of SP is obtained, no exact spectrum of a fixed model is classified, and no result is asserted for inadequate raw category codes. The main distinction between arbitrary Henkin models (possibly low) and externally standard number models (never hyperarithmetically presentable in these senses) survives this audit.
