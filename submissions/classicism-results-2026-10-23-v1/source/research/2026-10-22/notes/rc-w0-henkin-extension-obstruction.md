# The unrepresented fixed reservoir: what compactness and EM constructions must preserve

OpenAI Codex research audit, 22 October 2026. This is a construction audit, not a C model or a proof of Relational Choice ⇒/⇏ Transversal Choice. No repository record was changed.

## 1. A concrete countable symmetry skeleton

For the obstruction analysis it is enough to use a countable group of shears. Let

    M = W₀ ⊕ (⊕_{i∈N} Qbᵢ) ⊕ Qh,
    H = Qh,
    E(x,y) iff x−y∈H.

Here W₀ is an externally fixed Q-vector space, of arbitrarily large dimension, not supplied as an object-language predicate. Let G consist of the shears which fix W₀ and h and send finitely many bᵢ to bᵢ+qᵢh. The coefficient list (qᵢ) has finite support. In particular τᵢ sends bᵢ to bᵢ+h and fixes the other displayed generators.

Suppose G acts by automorphisms of an entire intensional C structure, preserving actual evaluation and the named seed relation entities. Suppose every admitted entity has finite support over W₀. For any proposed E-transversal T, choose i outside its finite support. Then τᵢ fixes T and preserves the class bᵢ+H, while moving every point in that class. The unique T-member of that class would have to be fixed by τᵢ, a contradiction.

The no-transversal invariant is consequently very concrete. It needs neither an uncountable automorphism group nor a metatheoretic quotient object. The unresolved task is to construct the whole typed hierarchy, including its choice graphs, while preserving this action and finite support.

## 2. Finite support is not preserved by ordinary compactness

There is a concrete example of the loss, even when support in the limit may use the entire ultrapower atom sort. Let the atom sort be

    D = W₀ ⊔ {aᵢ,bᵢ : i∈N},

where G=⊕ᵢ C₂ fixes W₀ pointwise and its ith generator τᵢ swaps aᵢ,bᵢ. Let the entity sort be Fin(D), with membership as evaluation. Every entity has a finite atom support: its own finite set of members suffices. This is an example about supported structures, not a C model.

Take a constant sequence of copies of this structure and a nonprincipal ultrafilter U on N. Act on the ultrapower **coordinatewise by the same fixed group G**. For each n put Aₙ={a₀,…,aₙ}. The ultrapower entity A=[Aₙ] is moved by every τᵢ, since τᵢAₙ≠Aₙ for all n≥i. The sizes of the original supports are unbounded.

Nevertheless every atom d=[dₙ] in the ultrapower is moved by at most one τᵢ. Indeed, τᵢ moves d exactly when {n : dₙ∈{aᵢ,bᵢ}} belongs to U. These sets are pairwise disjoint, so at most one belongs to U. Any finite tuple of ultrapower atoms is consequently fixed by all but finitely many τᵢ. Choose a remaining i: τᵢ fixes the proposed support tuple but moves A. Hence A has no finite atom support, even allowing nonconstant ultrapower atoms as support parameters.

This disproves only the unrestricted inference “all approximating structures have finite support, therefore their ultraproduct limit does too.” It does not say that all ultraproducts fail, or that a uniformly supported or specially generated limit cannot work. W₀ remains pointwise fixed in this example. The example uses pair swaps rather than linear shears; the actual proposed C construction must separately preserve the outside-W₀ linear shears of §1. In particular, one cannot assume that arbitrary ultrapower vector parameters preserve the moving-class argument: their induced action and fixed sets require fresh verification.

Saying that an entity has some support of ordinary finite length is an external disjunction over all finite lengths. A first-order finite-sequence encoding can instead produce nonstandard finite supports. Merely adding support sorts or support predicates therefore does not fix the problem unless standard finite generation is separately proved.

An EM or term-generated construction can enforce external finite generation: each entity is the value of a finite term in finitely many skeleton parameters. But that leads to a distinct obligation in the ground sort.

## 3. The individual-hull obstruction for an EM/Skolem construction

Automorphisms of an EM skeleton extend to its Skolem hull by acting on term parameters. Consequently every term with parameters fixed by a skeleton automorphism is fixed by that automorphism. This gives the desired finite support of **terms**, but it does not guarantee that newly added individual terms retain the prescribed vector-space action.

The missing requirement is:

> Every individual value generated from a finite presentation tuple A lies in the preassigned vector hull W₀+span_Q(A,h), and the induced action on that value is the actual linear shear action.

Without this requirement, Skolemization may add a new individual in the E-class bᵢ+H that is fixed by τᵢ. Such a point destroys the moving-class argument. It is not enough that all the original named points bᵢ+qh are moved.

The failure is especially explicit if one starts from a theory already asserting TC. A metatheoretic Skolem term T(E) for a transversal is fixed by every symmetry fixing E. Its unique member in bᵢ+H is then fixed by τᵢ. In the preassigned vector space there is no such fixed member. Thus one cannot simultaneously retain that Skolem witness, the linear-hull requirement, and the protected shear. An EM construction from known TC models must give up at least one of them.

This is different from the already identified internal-ε trap. Here the Skolem functions can remain outside the C object language, so no forbidden typed operation has been introduced. The problem is their effect on the actual individual domain and automorphism action.

## 4. The exact extension obligation

A genuine Henkin construction would need the following extension property for its **finite partial diagrams**, rather than a generic appeal to compactness:

* Extend a supported partial typed application/truth diagram by a graph entity S selecting from a requested serial relation U.
* Extend it simultaneously by the finitely many currently requested lambda values, quantifier witnesses/counterwitnesses, and required H-equivalence identities involving S.
* Preserve the prescribed finite partial shear actions and the individual-hull condition of §3.
* Keep previously assigned selector values compatible with every subsequently admitted input code.

The elementary graph part has an exact test. If K is the subgroup fixing the intended support of S and U, an equivariant selector requires, for every input code x, a fiber witness y fixed by K_x. Conversely these witnesses allow orbitwise definition of an equivariant external graph. The difficult preservation step is ensuring that the newly reified graph and all new lambda/quantifier codes do not create a nonempty K_x-invariant fiber without any such witness. The moving-complement and S-generated-span examples in the other notes show this can genuinely fail.

The requirement is more concrete than postulating a finished C+RC model: it asks for extension of an explicitly finite collection of typed equations, truth conditions, and partial automorphism constraints. But it is **not proved here**. In particular, freshness of elements of W₀ handles finitely many algebraic exclusions only; it does not by itself satisfy arbitrary higher-order quantified constraints or prove their compatibility with H-equivalence.

A fair Henkin construction using an actually proved extension lemma of this form could preserve finite term support directly, avoiding the compactness defect in §2. Without that lemma, a first-order compactness statement simply moves the main consistency question into finite satisfiability.

## 5. What known generic Skolemization supplies—and does not supply

Kruckman–Ramsey, *Generic expansion and Skolemization in NSOP₁ theories*, arXiv:1706.06616v2, §4.3, Corollary 4.9, constructs expansions with built-in Skolem functions under its stated model-theoretic hypotheses; §4.2 treats the generic expansions. [Primary source](https://arxiv.org/pdf/1706.06616).

That theorem preserves the specified classification-theoretic property. It does not establish the protected shear action, the vector individual-hull condition, graph reification into simple types, or preservation of C's higher-order lambda/quantifier semantics. None of those requirements has been verified by an application of that theorem here.

The conclusion is therefore an obstruction and a precise missing lemma, not a model claim: ordinary compactness loses finite support; unrestricted Skolem hulls can add fixed representatives in the very classes that must stay moved; a support-preserving, individual-hull-preserving typed Henkin extension theorem would have to address both failures together.
