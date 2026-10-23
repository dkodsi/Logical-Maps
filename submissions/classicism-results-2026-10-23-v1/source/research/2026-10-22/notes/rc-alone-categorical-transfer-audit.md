# Categorical choice and quotient completions: exact transfer audit

OpenAI Codex, 22 October 2026. Ordinary mathematical/source audit; no repository changes or formalization. Target: a model of Bacon–Dorr C with all-type Relational Choice but without Transversal Choice. No such model is established here.

## 1. Conclusion

The examined categorical literature gives genuine choice-versus-quotient phenomena, but none gives the required C model by an existing equivalence alone. Three precise distinctions block the immediate transfers:

1. The papers' abbreviation **RC** means *Rule of Choice*, selecting a base-category arrow. It is not the map's graph-valued Relational Choice.
2. Weak function spaces generally lack the substitution and eta laws required for C. Quotient completion can repair function spaces, but that is a new model whose selection principles must be checked again.
3. The most concrete **Boolean** assembly example actually admits an especially simple, fully extensional interpretation of every type in C's restricted relational type system. That interpretation has Transversal Choice in the ordinary choice metatheory. Its failure of choice for numerical operations uses an excluded individual-returning type, not a counterexample to C's principles.

The third point strengthens and qualifies the second: saying merely that partitioned assemblies lack general exponentials would miss C's specific type restriction.

## 2. Primary-source ledger

The following are the inspected results, with locations in the linked versions. Statements below use the authors' categorical terminology, not the identically abbreviated map principles.

**Maietti–Pasquali–Rosolini, 2019.** *Elementary Quotient Completions, Church's Thesis, and Partitioned Assemblies*, LMCS 15(2), article 21. Remark 1.3, p.21:5, says weak hyperdoctrines do not generally support eta or substitution inside lambda terms. Definitions 2.1–2.2, pp.21:8–9, distinguish arrow-selecting rules from internally quantified choice axioms. Proposition 2.9, p.21:10, transfers AC to AUC under quotient completion. Section 4, pp.21:14–17, defines partitioned assemblies and the Boolean doctrine PΓ; Lemma 4.2 proves choice for the different doctrine ΨPAsm. Remark 4.11 records failure of AUC and AC in the Boolean strong-subobject doctrine of assemblies. [Primary published PDF](https://lmcs.episciences.org/5597/pdf).

**Maietti–Pasquali–Rosolini, 2017.** *Triposes, exact completions, and Hilbert's ε-operator*. Definition 5.5, linked manuscript p.18, selects an arrow from an entire relation. Definition 5.10 and Example 5.14, p.21, define epsilon and give well-order-frame examples. Theorem 5.15, p.22, identifies epsilon with the Rule of Choice after comprehension completion. Corollary 6.3 and Theorem 6.6, p.25, relate this to exact completion and demonstrate nonpreservation of epsilon by tripos-to-topos. The counterexamples are non-Boolean. These are manuscript page numbers, not the journal's pp.141–166. [Author's revised PDF](https://www.math.unipd.it/~maietti/papers/mpr_tmj_rev.pdf).

**Maietti–Rosolini, 2016.** *Relating quotient completions via categorical logic*, author version dated 16 June 2016. Proposition 4.11, p.17, identifies the Rule of Choice in a doctrine with comprehensions with the Rule of Unique Choice in its elementary quotient completion. Section 6, pp.18–20, treats the corresponding internally expressed axioms. [Primary author PDF](https://www.math.unipd.it/~maietti/papers/rqcvcl-rivisto.pdf).

**Dagnino–Pasquali, 2026 preprint.** *Projective covers, doctrines of algebras and the relational quotient completion*, arXiv:2608.01915v1, 3 August 2026. Theorem 3.7 and Corollary 3.8 characterize extensional quotient completions using projective covers. Section 4.2, especially Proposition 4.14, identifies all objects being projective with splitting all quotient arrows. These are results about relational doctrines and their base arrows; the hypotheses do not supply C's proposition type or higher-type lambda structure. [Primary preprint, inspected HTML](https://arxiv.org/html/2608.01915v1).

## 3. Why the choice equivalences are not already RC versus TC

Write graph choice for the map's principle:

    entire R ⊆ A×B  ⇒  an entire functional S ⊆ R.

The cited Rule of Choice instead requires

    entire R ∈ P(A×B)  ⇒  an arrow f:A→B with R(a,f(a)).

Their Rule of Unique Choice says an entire functional relation is the graph of a base arrow. Thus Rule-of-Choice to Rule-of-Unique-Choice transfer is not a theorem equating our graph choice with our transversal choice. It changes the distinction between represented relations and represented operations.

This is also a warning against repairing weak exponentials indiscriminately. Suppose an interpretation gives coherent C lambda/application, represents the required generic relation objects, and carries the arrow-selecting rule through comprehension contexts to internally quantified operation choice. At each permitted output type τ≠e it then supplies **Functional Choice**, not merely Relational Choice. In the local proved records:

    Functional Choice ⇒ Relational Choice,
    Functional Choice ⇒ Plenitude ⇒ Actuality ⇒ Transversal,
    Transversal + Relational Choice ⇒ Transversal Choice.

Consequently this strong transfer, if achieved, would destroy the proposed separation. If the categorical arrow selection is only an external rule, one must instead check its internalization; that check cannot be omitted or treated as automatic in a nonstandard interpretation.

## 4. A concrete original check: the Boolean assembly example gives TC

This argument uses the underlying-set definition of assemblies and PΓ in the 2019 paper, but the analysis of the exact C reduct is our own.

For a set S, define K(S) to be the partitioned assembly whose underlying set is S and whose assigned realizer is the same fixed natural number 0 for every element. For every partitioned assembly A:

    Hom_PAsm(A,K(S)) ≅ Set(ΓA,S).

Indeed, every set function to K(S) is tracked by a constant recursive program returning 0. Conversely an assembly arrow is, by definition, an underlying set function. The bijection is natural, so Γ is left adjoint to K. Γ preserves finite products.

For any A and S, a **genuine exponential**, not just a weak one, is therefore

    K(S)^A ≅ K(S^(ΓA)).

Proof: for every X, naturally in X,

    Hom(X×A,K(S))
      ≅ Set(ΓX×ΓA,S)
      ≅ Set(ΓX,S^(ΓA))
      ≅ Hom(X,K(S^(ΓA))).

Now interpret e by any nonempty partitioned assembly E and t by K(2). Every arrow type admitted by C has relational codomain. Induction on types gives

    Γ(t)=2,
    Γ(σ→τ)=(Γτ)^(Γσ),
    D_τ=K(Γτ) for every relational type τ.

Thus every admitted C function space is the full underlying set function space, although PAsm is not cartesian closed for arbitrary codomains. In particular the problematic general type e→e is never needed.

In PΓ, predicates are arbitrary subsets of underlying sets. Connectives, quantifiers and diagonal equality have their ordinary two-valued meanings. The displayed exponentials supply coherent beta, eta, substitution, and currying; equal predicates have the same characteristic function. Hence Logical Equivalence holds, and the interpretation satisfies the stronger actual Extensionality as well.

Given any represented actual equivalence relation R on any admitted type σ, ordinary external set-theoretic choice selects one element of each R-class. The resulting subset T⊆Γσ has a characteristic function Γσ→2, which is an element of the admitted σ→t type. This is exactly the required C transversal. The same observation gives graph choice. This conclusion is relative to the ordinary choice metatheory used in this analysis; it asserts no choiceless-metatheory theorem.

For ordinary assemblies rather than partitioned assemblies, the standard chaotic assembly ∇S has the analogous adjunction Γ⊣∇. Its Boolean strong-subobject classifier is ∇2. The identical exponential calculation gives the same extensional C reduct in the strong-subobject interpretation.

Therefore neither the Boolean PΓ example nor the Boolean strong-subobject assembly example supplies RC+¬TC in this standard interpretation. Their failure to turn every functional numerical relation into a tracked numerical operation does not contradict this: numerical operations have type e→e, which is absent from the fixed C type system. Even in a larger type language, failure of operation extraction is different from failure to represent a functional graph or a transversal subset.

### A nonsplit quotient with an admitted transversal

There is an explicit original example showing why categorical quotient choice must not be identified with C-TC here. Choose a nonrecursive nonempty proper subset K of the natural numbers. Let N be the usual partitioned natural-number assembly, and let Y be the two-element assembly with realizers K for its element 0 and the complement of K for its element 1.

The underlying function q:N→Y sends each number to its K-membership class. It is an assembly arrow tracked by the identity program. It is the categorical quotient of the equivalence E(n,m) saying that n and m have the same K-membership: if a tracked arrow h out of N is constant on these classes, its underlying factor through Y is tracked by the very same program, since a realizer for a class is one of its members.

This quotient has no assembly-arrow section. A tracked section would send the two classes to distinct representatives k₀∈K and k₁∉K. Its tracker would be a total recursive program whose output on input n is k₀ if n∈K and k₁ otherwise. Comparing its output with k₀ would decide K.

Nevertheless {k₀,k₁} is a represented transversal subset of N in the Boolean strong-subobject doctrine, and its characteristic function is an admitted C property. Thus this is genuinely a categorical nonsplitting phenomenon alongside transversal existence. It separates arrow extraction from graph/subset existence, not Relational Choice from Transversal Choice over C.

## 5. Another original check: Boolean localic epsilon degenerates

The 2017 epsilon examples use a frame H with the doctrine X↦H^X over nonempty sets. Epsilon requires each existential supremum to be attained by a selected element.

Suppose instead that H is Boolean and this doctrine has epsilon. For any a∈H take X=1, Y={0,1}, and the predicate with values

    α(0)=a,    α(1)=¬a.

Its existential value is a∨¬a=1. An epsilon arrow 1→Y selects either 0 or 1, and its defining equality requires the selected value to be 1. Therefore either a=1 or ¬a=1, i.e. a∈{0,1}. Every element of H is trivial, so a nondegenerate H must be the two-element Boolean algebra.

This does not rule out Boolean epsilon doctrines generally. It rules out replacing the non-Boolean frame in the paper's specific localic example by a nontrivial Boolean algebra while preserving the claimed epsilon property. It therefore blocks that immediate classical adaptation of the published nonpreservation example.

## 6. Exact remaining equality obstruction

A posetal doctrine identifies logically equivalent **predicates in a fibre**. C needs identities between **proposition and relation entities**. These are not automatically the same equality.

If Ω is merely a weak classifier, two arrows Γ→Ω can classify the same fibre predicate. The doctrine's posetal equality does not identify those arrows or the corresponding entity names. Choosing representatives externally does not establish substitution under abstraction, eta, or Logical Equivalence on those names. This is the categorical version of the earlier raw-realizability transfer gap.

There is a precise overcorrection to avoid. If the interpretation takes abstraction to be an inverse to the semantic classification map on *all* fibre predicates, and beta and eta make these maps inverse in every context, then it has upgraded weak classification to unique classification. Under the standard internal interpretation this gives extensional predicates. In a topos with its usual power objects and internal equality, this is the ordinary extensional higher-order interpretation; RC then yields TC. This observation does not prohibit a different, explicitly constructed intensional interpretation. It shows why simply normalizing all predicate codes is not such a construction.

The projective-cover equivalences do not fill the gap. A cover supplies lifts of arrows out of projective objects; it does not assert that the projective objects are closed under every required relational function type, nor that chosen lifts respect C's lambda identities. Moving to the completion can produce coherent function spaces, but its new quotient objects and equality may change the choice verdict. An equivalence of the completed doctrines alone supplies no preservation theorem for the proposed intensional C reduct and its literal entity identities.

## Verdict

No primary-source construction examined here supplies the requested classical C model with RC and failure of TC. There are genuine categorical choice/quotient distinctions, but their known equivalences do not bridge the exact typing and identity requirements. The concrete Boolean assembly candidate is positively ruled out in its natural C interpretation by the full-function-space calculation above; the localic epsilon candidate cannot be made nontrivially Boolean in the suggested way. These are transfer obstructions, not a proof that RC implies TC over C.
