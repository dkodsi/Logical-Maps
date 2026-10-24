# An effective Gallin representation for the positive package

Original reconstruction and audit by GPT-6 (OpenAI), 22 October 2026. This strengthens the scope of the representation in `rigidity-actualization.md` §§13–14; it does not attribute a new theorem to Gallin. Ordinary mathematics only. No main database edits, human-check claim, or Lean claim.

## 1. Claim and exact coding boundary

Write B for C + boxed Plenitude, equivalently C5 + propositional Atomicity. Let H0 be the recursive many-sorted extensional relational Gallin theory in `positive-effective.md` §3: base sorts e,s,o, exactly two Boolean truth values in o, function types ending in o, extensionality, and comprehension for every auxiliary first-order formula. Add a designated world constant w0.

**Representation theorem.** Every B BBK model, at its designated evaluation, is isomorphic as an interpreted original typed structure to the original-language reduct of an H0 model. The construction is internal to the original domains and is a Henkin construction, not an external fullness assertion. It preserves the interpretation of every original term and formula.

For countable presentations, assume the source code supplies:

1. uniformly numbered typed domains with decidable membership and identity, using injective labels or fixed canonical representatives;
2. interpretation of every original finite term under every finite typed parameter assignment;
3. the truth valuation on proposition entities.

Then a complete elementary diagram of the auxiliary representation is uniformly computable from that code. With the inherited numbering specified in §5, that diagram computes the exact original operational code as well. Thus an auxiliary representation can be chosen with the same Turing degree as the specified source code. Here the code degree means the canonical join of domain membership, identity, term-value graphs and truth data, not arbitrary oracle/program padding. Alias choices may otherwise conceal information unrelated to the structure. This is a representation-level statement; it says nothing about an arbitrary weak category/action reduct lacking term interpretation. Section 8 removes the valuation input for a precisely qualified reconstruction theorem.

Conversely a complete elementary diagram of an H0 model computes its original-language reduct with precisely these operations and truth. These are uniform transformations of codes. They strengthen the earlier positive *existence* result without relying on an unspecified effective conversion of action categories.

## 2. Auxiliary domains and comprehension

In a B model M, take the target e-domain to be all original individuals, the s-domain to be the original propositional atoms, and the o-domain to be {bottom,top}. The three domains remain different *sorts*, even where underlying original values overlap. Let r replace target e by original e and both s,o by original t, recursively on arrow types.

Each target domain is represented by a predicate H_alpha on the corresponding original type r(alpha). At base types use the domains just stated. If alpha=alpha_1...alpha_n o, take

    H_alpha(F) := Rigid(F) and
                  F <= lambda x_1...x_n . AND_i H_alpha_i(x_i).

The base predicates are rigid under C5. By induction, these supported rigid domains are nonempty, rigidly definable, and closed under application. If two of their relations agree on their core arguments, they also agree off those arguments, because both vanish there; hence they are identical. This supplies target extensionality.

An auxiliary first-order formula with target parameters translates to an original formula by bounding each quantifier with its H-predicate and using original equality and application. Induction on formulas makes its value bivalent at target assignments. The quantifier step uses C5's BF: all true matrix instances are necessary, and all false core/noncore conditions are stable. Therefore the raw supported matrix

    lambda xbar . (AND_i H_alpha_i(x_i)) and phi*(xbar)

is rigid and supported. It is an admitted original lambda term and lies in the target predicate domain. This proves every auxiliary comprehension instance. It does not require Actuality to import an arbitrary noncore formula: it applies to the intrinsic auxiliary translation, whose bivalence was proved by induction.

The intended target truth values are the two literal original entities bottom and top. Its first-order application functions are restrictions of original application. The preceding argument constructs an H0 model.

## 3. Original types and the inverse representation

Translate original types by

    T(e)=e, T(t)=s o, T(sigma tau)=T(sigma) T(tau).

For sigma=e use identity substitution, never a forbidden original ee term. For tau=sigma_1...sigma_n t define

    j_tau(F)[a'_1,...,a'_n,w] :=
       Atom(w) and exists a_1...a_n .
       (AND_i j_sigma_i(a_i)=a'_i) and w<=F[a_1,...,a_n];

    k_tau(R)[a_1,...,a_n] :=
       exists w . R[j_sigma_1(a_1),...,j_sigma_n(a_n),w] and w.

All functions actually used have relational outputs, so they are original admitted terms. Order and identity are bivalent under C5, and BF closes their existential quantifiers; hence j has values in H_T(tau). The supported graph proof audited in `audit-rigidity-and-bottom-cut-20261022.md` gives

    k_tau(j_tau(F))=F,
    j_tau(k_tau(R))=R  for H_T(tau)(R).

The equations are proved by induction on original types. Atomicity supplies reconstruction from atoms, and support supplies equality off the represented domains. Thus j_tau is a bijection from the original tau-domain onto the whole target T(tau)-domain, not merely an injection into a selected subdomain.

The maps preserve application, and therefore preserve abstractions by target extensionality and surjectivity of the argument maps. The Boolean clauses are pointwise on atoms. For quantification the needed equation is

    w <= forall x Xx  iff  forall x . w<=Xx,

for atomic w; its reverse implication is BF, and its forward implication is modal universal instantiation. Equality is translated to target extensional equality by injectivity of j and the C5 bivalence of original identity.

B gives Actuality and exactly one true propositional atom w0. For any original p,

    p is actually true iff w0<=p iff j_t(p)(w0)=top.

This identifies the original designated truth valuation with the target-world evaluation. Induction on original syntax establishes the full interpretation-preservation claim. No representation of an original model satisfying only unboxed ND, or only Atomicity, follows from this proof.

## 4. Computing the auxiliary diagram from an original code

Each H_alpha is an effectively constructed original formula obtained by recursion on a finite target type. Given a source entity number a, term interpretation computes H_alpha(a) and the source truth map decides its value. Thus every target sort is a decidable subset of a source sort, relative to the source code. Application and literal identity are likewise computable.

For any auxiliary first-order formula phi and target parameter assignment, the bounded translation phi* described in §2 is effective. Its actual source truth is exactly the target satisfaction value. This computes the **complete** elementary diagram, including auxiliary quantifiers, rather than merely the atomic diagram.

The designated w0 is obtained uniformly: enumerate the source proposition domain and test Atom(a) and a. B guarantees the search succeeds. Uniqueness is already established mathematically; deciding that no second witness exists is unnecessary.

All constructions use finite strings and oracle queries to the supplied code. No powerset enumeration, external full model, or infinitely large search tree is generated.

## 5. Numbering is essential for the reverse degree claim

If every target entity is numbered merely by its ambient source code, the reverse construction immediately returns an *isomorphic* source copy, but not necessarily the original numbering. That suffices for model existence, not automatically for equality of the two supplied code degrees. Use the following explicit repair.

The type map T is syntactically injective with decidable image. On each image sort T(sigma), number the target element j_sigma(a) by the original number a of the source sigma-domain. On target sorts outside the image of T, use tagged ambient-source numbers satisfying H_alpha. Thus original and inherited numbering are literally aligned on every translated sort. Converting inherited numbers to ambient core representatives uses the term j_sigma; converting an ambient H_T(sigma) member back uses k_sigma. Both are computable by the source term interpreter. This transports all target operations and diagram queries effectively.

From the resulting target complete diagram, recover each original typed domain and identity directly from its T-image sort. To interpret a source term A under numbered parameters, effectively translate it into the auxiliary language. If lambda/quantifier operators are not named in the first-order signature, use the effective formula defining its unique value: application is explicit, lambda values are characterized by their equations at every argument, and logical constants by their truth tables/quantifier clauses. Comprehension proves existence, and extensionality proves uniqueness. Search the numbered output sort using its complete diagram until that unique value is found. By the inherited numbering, its number is exactly the number produced by the original interpreter. Truth of p is recovered from app(p,w0)=top.

Consequently the auxiliary diagram and original code compute one another for this constructed numbering. A diagram of some arbitrarily renumbered representation need only yield an isomorphic original copy; no stronger invariance under arbitrary external renumbering is asserted.

## 6. Choice and optional original assertions

Because the original reduct is isomorphic to M, every optional original sentence is preserved, including either quantified Frege Infinity axiom, its box, failures of Functional Choice, and all original schema instances. The representation does not conflate original Infinity with an informal assertion of external infinitude of the new world sort; the separate §17–19 transfer proofs address those comparisons.

If M additionally satisfies original Functional Choice, its auxiliary core satisfies the relational-output auxiliary Functional Choice schema H_ch. Given an auxiliary serial relation with input alpha and output beta ending in o, view its core codes as original r(alpha),r(beta) entities. Extend the relation off H_alpha by a fixed core output. Ambient FC supplies a selector f. On core inputs its values are already H_beta-members. Mask f by H_alpha and by the remaining core support predicates, giving bottom outside support. At all current supported tuples its output is bivalent, and at other tuples it is bottom; C5 and BF make this masked relation rigid. It is therefore a target operation with the prescribed core values. This direct argument avoids an unnecessary appeal to actualization for this functional-choice transfer.

The converse original-FC validity in H_ch is the direct argument of `positive-effective.md` §4.3. Thus the positive Choice package also has the representation and effective conversions above. Its consistency remains separate from the complexity comparison, as witnessed by the full models already recorded.

## 7. Scope and attribution

This is a refinement of the session's internal representation proof and an independently checked coding argument. The nominal/Gallin auditor checked the forward diagram reduction and identified the numbering qualification in §5; that qualification is retained rather than hidden in the phrase “degree preserving.” No exact degree spectrum of a fixed isomorphism type is classified.

The proof uses the fixed C theory, the recorded consequences of boxed Plenitude, and the new explicit maps from `rigidity-actualization.md`. It establishes that the auxiliary Gallin model theory covers all adequately interpreted positive BBK models, not only a convenient model subclass. It neither represents Max as a Gallin model nor converts an arbitrary category/action code at unchanged degree.

## 8. Equality-only reconstruction and two-sided model recovery

The independent audit `audit-effective-representation-coding-20261022.md` verifies §§5–6 and strengthens the input condition. Intrinsic auxiliary formulas translate to bivalent original propositions. Their truth is therefore decided by comparing their term value with top; no original designated truth map is needed for the auxiliary complete diagram. Atomhood is likewise bivalent, so equality and parameterized term interpretation uniformly find a propositional atom a by enumeration. Define val_a(p) by the algebraic equality a∨p=p.

This gives a uniformly computed auxiliary representation and a repointed original model with exactly the same operational structure. An atom-transposition automorphism proves the repointed model is isomorphic to the original as a pointed **pure** model. It need not preserve arbitrary nonlogical constants. Without the index of the originally true atom, the construction does not uniformly recover its exact truth map. Nonuniformly the original truth map is still computable from the operational code by hard-coding that finite atom index. With inherited numbering, the auxiliary diagram therefore has precisely the operational-code degree, which also equals the degree of the original full code. Supply the original truth map or its true atom index for uniform recovery of the originally designated valuation.

The Gallin auditor's `gallin-biinterpretation-20261022.md` proves the other model-level composite as well: starting with any H0 model, passing to its C reduct and then recovering the hereditary rigid core returns an isomorphic H0 model at every auxiliary sort, including sorts outside the type-translation image. The recursive maps send worlds to singleton propositions, Booleans to constant propositions, and relations to supported constant-world graphs. Comprehension and extensionality give their inverse equations; no Choice or fullness is assumed.

This two-sided reconstruction is a theorem about the specified many-sorted presentations and their definable isomorphisms. It does not by itself preserve arbitrary original numbering on every auxiliary sort: different auxiliary sorts can collapse to the same ambient original code type. The exact original-to-auxiliary degree theorem above uses its explicit inherited numbering. A later deliberate-numbering lemma in `gallin-biinterpretation-20261022.md` §7 repairs the reverse direction too: lift each auxiliary sort's core codes by iterated haecceities into pairwise distinct original types, use even labels for the embedded original auxiliary labels and odd labels for the complement, then decode formulas through the unique inverse graphs. Image membership is decided by the source complete diagram. This proves exact degree preservation for a deliberately presented original reduct of every supplied auxiliary model. It remains false to infer that every naïve reverse reduct with arbitrary preexisting labels preserves all that numbering information.
