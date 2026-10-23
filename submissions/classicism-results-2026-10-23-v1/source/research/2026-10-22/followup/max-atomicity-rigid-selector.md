# A rigid Boolean algebra route to pure Maximalism versus Atomicity

22 October 2026. New mathematical argument by OpenAI Codex; direct source: misc, this note. Status: proposed proof, self-audit completed, not independently checked or entered in the database. The language throughout is the original **finitary pure relational language of C**. Sections 2–5 construct the selector inside L. Section 7 gives an alternative directly in the ambient ZFC universe, removing the constructible-order step. Neither route adds V=L, Choice, a selection constant, or infinitary syntax to C.

The claim being checked is that a single closed pure identity follows from Atomicity_t but not from C. Pure Max(C) then asserts its negation. The key is a pure definable selector in a particular full Boolean-valued C model, rather than a selector available in every C model.

**Proposed conclusion:** pure Max(C) implies ¬Atomicity_t, and therefore also excludes unboxed all-relational-type Atomicity. Both finite-language routes below produce the required separating identity.

**Reading route.** For the direct ZFC version, use the obstruction in §1, the Boolean-valued interpretation clauses in §2, the HCode lemma in §3, and the concrete selector in §7. In that version all domains and cardinalities are computed in ambient ZFC, as §7 specifies. Sections 4–5 give an alternative selector using L and the same coding lemma. Both are ordinary mathematical arguments; neither has received an independent audit.

**Further audit, 22 October 2026.** The [finite selector audit](max-atomicity-selector-audit.md) supplies the direct route's finite definitional library, the size and absoluteness checks for each construction, and a weaker Cover predicate that can replace HCode in §7. Its §9 also gives a shorter algebraic non-theorem certificate using the atomless algebra directly; the ordinary pointed model here remains intact. The audit records two presentational corrections incorporated below: crispness belongs to the guarded code as a whole, and W's lambda closure is the closed expression. The proposed status is unchanged.

## 1. The bounded splitter obstruction

For b^t and F^{tt}, put

    Split_b(F) := ∀p^t [(p≠0 ∧ p≤b) →
                         (p∧F(p)≠0 ∧ p∧¬F(p)≠0)].

**Lemma.** C proves

    Atomicity_t → ∀b^t ∀F^{tt} (b∧Split_b(F) = 0).

Both outer quantifiers are unboxed. This strengthens the obstruction in [max-atomicity, §8](max-atomicity.md).

**Proof.** Suppose b∧Split_b(F) is nonzero. Atomicity supplies an atom w below it. In particular w≤b and w≤Split_b(F). At a possibility where w is true, the transported w is nonzero and below b, and Split_b(F) is true. Thus w∧F(w) and w∧¬F(w) are both nonzero there. Each is a current Boolean part of w. Neither can be zero here, because NI would make that equality to zero necessary. This contradicts current atomhood. Equivalently, use atomhood first to see that one of these two parts is zero, necessitate that particular equality by NI, and contradict the split at the w-possibility. No Barcan or Choice principle is used. ∎

The same reasoning has a useful algebraic formulation without Atomicity. C proves

    Split_(b∧Split_b(F))(F).

For a nonzero p below the displayed guard, p≤b persists by NI and p necessitates Split_b(F). A p-possibility therefore witnesses both parts of p as nonzero; either part's being zero currently would persist by NI and contradict that witness. Thus every current nonzero part of the guard has two current nonzero parts. Atomicity forces the guard itself to be zero. This proves the lemma syntactically using ordinary necessitated instantiation, NI and the Boolean laws; no model-completeness assumption enters.

It therefore suffices to find CLOSED PURE terms b,F such that C does not prove `b∧Split_b(F)=0`. We need not have a global splitter, and b need not be actually true in the model witnessing this non-theorem.

## 2. The full Boolean-valued C model

Work internally to L. Choose a nontrivial complete atomless rigid Boolean algebra A. The existence input is Jech–Shelah, *A Complete Boolean Algebra That Has No Proper Atomless Complete Subalgebra*, Journal of Algebra 182 (1996), pp. 748–755: the theorem and corollary on p. 749 give a rigid completion and a simple complete algebra. The paper explains rigidity on pp. 748–749. [Primary source](https://shelah.logic.at/files/95558/566.pdf). Its ZFC construction can be carried out in L.

Put B=2×A, a=(1,0), and b_0=(0,1). B is complete, has a as its unique atom, and has atomless interval below b_0. B is also rigid: every automorphism fixes its unique atom and its complement; its restriction to the latter interval is an automorphism of A, hence the identity. Decomposition into the two coordinate parts then fixes every element of B.

Use the full Boolean-valued construction already proved in [the local write-up, §§1–2](../../../topics/classicism/writeups/full-boolean-valued-atom-and-atomless.md):

    D_e={*}, D_t=B, D_(στ)=D_τ^(D_σ)   (τ≠e).

All these sets and function domains are formed in L. Connectives are Boolean operations, quantifiers are arbitrary meets and joins, and equality at EVERY type is crisp: its value is 1_B for literal equality and 0_B otherwise. Actual truth is first-coordinate projection, a complete Boolean homomorphism. These clauses validate H and its ordinary truth clauses. Boolean soundness of an H-equivalence makes the associated abstractions literally equal functions, validating Logical Equivalence and therefore C. The construction background is Bacon, *Could the truths of mathematics have been different?*, online appendix §B.2, pp. 7–9 (PDF pp. 41–43), as recorded in that write-up; the rigid choice of A and the selector below are the present argument.

The whole typed model is a set in L. Its satisfaction of each finitary C sentence is absolute to the ambient universe: its domains and interpretation functions are fixed sets. We use L-full domains, not a claim that these domains remain full with respect to any additional ambient subsets. Thus the argument uses ordinary ZFC metatheory and does not require the ambient universe to satisfy V=L.

We will define a closed pure term b which denotes b_0, and a closed pure F which selects a nonzero proper part of every non-atomic proposition in this particular model.

## 3. A finite pure code for H_(κ+)

Set U:=tt and let κ=|B|, calculated in L. Then |D_U|=κ^κ=2^κ. The set H_(κ+) of sets with transitive closure of cardinality at most κ also has cardinality 2^κ. All cardinal statements in §§3–5 are internal to L.

The following definitions are abbreviations for single FINITE C formulas at FIXED types. They do not quantify over types or use an axiom scheme.

For X^{Ut}, write

    Crisp(X) := ∀u^U (Xu=0 ∨ Xu=1),
    Small(X) := ∃f^{Ut} ∀u^U v^U
                  [(Xu ∧ Xv ∧ f(u)=f(v)) → u=v].

For crisp X, Small(X) says that its extension injects into D_t=B. The f in Small is an arbitrary B-valued function, not a truth-valued subset code.

For E^{UUt}, define HCode(E) by the conjunction of:

1. E is crisp at every pair of arguments.
2. E is extensional: two elements with the same E-predecessors are equal.
3. E is well founded, expressed by saying that every nonempty crisp X^{Ut} contains an E-minimal element.
4. For every u, its predecessor predicate `λv.E(v,u)` is Small.
5. Every crisp Small X is a predecessor set: `∃u∀v(E(v,u)=Xv)`.

Extensionality and well-foundedness here are the ordinary first- and second-order formulas using E; all their displayed quantifiers have type U or Ut. HCode as a whole is crisp in the Boolean-valued model. For noncrisp E the first clause is zero. For crisp E, the remaining clauses use crisp membership and literal equality, with noncrisp X excluded by their guards; quantification preserves values in {0_B,1_B}. Full function domains supply every subset and injection required by these clauses.

**Coding lemma.** HCode(E) holds exactly when the set relation represented by E is isomorphic to `(H_(κ+),∈)`.

**Proof.** A well-founded extensional E has a transitive Mostowski collapse M. Clause 4 says that every member of M has at most κ immediate members. For any x∈M its transitive closure is the union of the sets reached by finitely many membership steps. Each level has cardinality at most κ, so |TC(x)|≤κ and M⊆H_(κ+). Conversely, by membership induction on x∈H_(κ+), all members of x belong to M. The set x is a subset of M of size at most κ. Clause 5 represents that subset by a member of M, which by transitivity and extensionality is x itself. Hence H_(κ+)⊆M.

For existence, choose a bijection D_U→H_(κ+) and pull membership back along it. Every predecessor set is small. Every subset of H_(κ+) of size at most κ has transitive closure of size at most κ, and so is itself in H_(κ+). This proves clause 5. The two cardinalities are 2^κ: P(κ) supplies the lower bound for H_(κ+), and coding each hereditary-κ set by a well-founded relation on κ supplies the upper bound. ∎

Thus the full model can quantify, using one fixed relation type, over codes for a canonical set universe of sufficient size. No code E is named or added to the language.

## 4. Canonically ordering a rigid Boolean algebra

Fix the standard parameter-free first-order set-theoretic formula χ(x,y) for Gödel's canonical order <_L. In L, `H_(κ+)=L_(κ+)`, and χ interpreted there gives the actual canonical order on that segment. The needed absoluteness is for a limit constructible level: comparisons between elements of the level agree with <_L.

For the finite formula χ and the comparison absoluteness, see Yurii Khomskii, *Regularity Properties and Definability in the Real Number Continuum*, ILLC Dissertation Series DS-2012-04, Fact 1.2.10(2) and the proof of Fact 1.2.11, pp. 14–15. [Author-hosted dissertation](https://www.math.uni-hamburg.de/en/personen/khomskii/papers/Yurii_Khomskii_PhD_Dissertation.pdf). We use only that order-formula fact. Well-foundedness of our code is supplied explicitly by HCode, not by a putative first-order axiom forcing all set models to be well founded.

Here are the size and absoluteness points used, rather than an assumption of an arbitrarily large coded universe. The inclusion L_(κ+)⊆H_(κ+) follows from the cardinalities of earlier L-levels. Conversely, the usual condensation argument takes a Skolem hull containing TC(x) and x, of size at most κ, in a sufficiently large L-level. Its collapse is an L_α of size at most κ, with α<κ+, and it fixes x. Thus x∈L_(κ+). For the order formula, the constructible levels, finite formula codes, their satisfaction relations and the canonical-order recursion up to any α<κ+ all have hereditary size at most κ. They are present in H_(κ+); their definitions and comparisons are absolute there. This is the standard finite definition of <_L, not an infinitary diagram of A or B.

Given E with HCode(E), translate χ and ordinary first-order definitions of sets, ordered tuples, and finite-signature Boolean-algebra codes by replacing membership with E and binding their variables at type U. Denote the translated order by L_E. All these formulas are crisp.

For a code c^U and h^{tU}, let Iso_E(c,h) be the finite formula saying that c codes a Boolean algebra and h is an isomorphism from the ACTUAL propositional Boolean algebra B onto its coded carrier. More explicitly, decode from c its carrier, zero, one, meet graph and complement graph; require that h is a bijection B→that carrier and preserves 0,1, meet and complement. Equality of arguments in B and of their h-values is literal equality, so this is the usual algebraic isomorphism condition. All coded operations are relations inside E; no set-valued output type has been introduced.

Let Candidate_E(c):=∃h Iso_E(c,h), and put

    Least_E(c) := Candidate_E(c) ∧
                   ∀d^U(Candidate_E(d) → ¬L_E(d,c)).

Candidates exist: take any ordinal-sized copy of B with its finitely many operation graphs. That code has hereditary size at most κ and hence belongs to H_(κ+). The canonical L-order has a unique least candidate, call its collapse C_0. This minimum does not depend on the representation E of H_(κ+).

Rigidity is used at exactly the next step. There is exactly one isomorphism from B to C_0: the composite of two such isomorphisms would be an automorphism of B. Pull the canonical L-order on the carrier of C_0 back through this unique isomorphism. This gives a well-order of B independent of E, c, and h.

It is defined by the following pure binary predicate; its lambda closure is closed:

    W(p,q) := ∃E^{UUt} ∃c^U ∃h^{tU}
                [HCode(E) ∧ Least_E(c) ∧ Iso_E(c,h)
                 ∧ L_E(h(p),h(q))].

In the model, W is crisp and denotes that well-order. Different presentations E do not introduce incompatible orders: their unique Mostowski collapses identify the same H_(κ+), the same least code C_0, and, by rigidity, the same map from B to C_0.

This is NOT a claim that rigidity alone gives first-order definability, nor a well-ordering theorem of C. It is a parameter-free higher-order definition which works in the particular L-full Boolean-valued model. The finite cardinal-bounded coding in §3 is what licenses the use of the canonical L-order.

**Type and symmetry check.** The only auxiliary quantified types needed for the coding are U=tt, Ut, UUt, and tU, all admitted relational types. The set-theoretic formula χ is translated at the single fixed type U. There are no free parameters for A, B, κ, L, a code, or an isomorphism. Dropping rigidity would invalidate the argument: for example, in a Boolean algebra with two interchangeable atoms, different isomorphisms to the same least code pull its order back in opposite ways. The existential union defining W can then relate the atoms in both directions. Rigidity is essential to the proof, not a substitute for an unmentioned choice of isomorphism.

## 5. The closed pure splitter and the separating identity

Write `0<q<p` for `q≠0 ∧ q≤p ∧ q≠p`. Define

    LeastPart(p,q) := 0<q<p ∧
                      ∀r^t(0<r<p → ¬W(r,q)),
    F := λp^t. ∃q^t(LeastPart(p,q) ∧ q),
    b := ¬∃p^t(Atom_t(p) ∧ p),
    Q := b ∧ Split_b(F).

These are finite terms of the original pure language after expansion of the fixed abbreviations. Only t and relational types built from t occur; no individual names or extra constants are used.

In the Boolean-valued model, LeastPart is crisp. If p is non-atomic and nonzero, it picks exactly one q, the W-least nonzero proper part. The Boolean join interpreting the existential in F therefore equals that q; if p has no such part, it equals zero. In particular F splits every nonzero p≤b_0, since that interval is atomless.

The formula Atom_t(p) is crisp in this model: its order and inequality tests are literal Boolean identities and its quantifiers are meets of crisp values. The only atom is a. Consequently `∃p(Atom_t(p)∧p)` has Boolean value a, and b denotes b_0. Every instance in Split_b(F) is true with value 1_B, so the universal formula has value 1_B. Therefore

    [[Q]]=b_0≠0_B,
    [[Q=0]]=0_B.

Thus C does not prove the closed pure identity Q=0, by the C model in §2. This does not infer consistency from a bare non-designated Boolean value: the identity Q=0 is FALSE at the designated ordinary evaluation, and Q≠0 is TRUE there. Equivalently, ◇Q is actually true there.

On the other hand, the lemma in §1, instantiated with the closed pure b,F, gives

    C + Atomicity_t ⊢ Q=0.

Pure Max(C) includes Q≠0, because the identity Q=0 is closed, pure and not C-provable. Hence the proposed conclusion is

    C + pure Max(C) + unboxed Atomicity_t is inconsistent.

The all-relational-type unboxed version would be inconsistent as well, since it implies Atomicity_t. This uses ONE ordinary pure Max instance, with reference theory C unchanged. It does not require signature Max, a new language, a schema of selectors, or any optional Choice principle in the object theory.

More concretely, the guard calculation in §1 would make this same Q a nonzero atomless interval in EVERY pure-Max model, uniformly split by the same closed pure F. It also identifies a direct obstruction to atomic pointed profiles: at any point satisfying Q, b is true and the profiles contain b and F, so every nonzero profile below b is split by another profile. Hence no such point has atomic B_t(v,a), for any individual marker a. This addresses the specific universal representation gap in the earlier follow-up.

## 6. Audit obligations and source boundary

The original full coalescence and finite/infinite-profile examples remain valid; they do not satisfy all Max instances. This argument targets the missing universal condition in the single-sentence criterion by producing the new candidate Q.

The nonroutine bridge is §4: the finite typed interpretation of canonical constructible coding must be read literally with the cardinal-bounded HCode of §3, crisp restricted predicates, and uniqueness from rigidity. Substituting mere rigidity for that bridge, silently adding a named selector, quantifying over types, or using an infinitary Scott diagram would not prove the stated result. The text supplies the bridge as a finite definitional expansion, while retaining χ as the standard fixed first-order definition of the canonical L-order.

The two imported ingredients are the sourced existence of a rigid complete atomless algebra and the previously verified full Boolean-valued C construction. The HCode, transport-free coding of W, bounded splitter lemma, and combination into Q are the present deductions. The constructible-order and condensation facts are standard set-theoretic inputs with their uses and size bounds spelled out in §4. No database or generated statement has been changed. No human or separate agent has checked this proof.

## 7. Direct ZFC variant: select the first splitting branch coordinate

There is a second way to perform the nonroutine bridge, without a canonical L-order or even a well-order of all propositions. It uses the EXPLICIT parameter-free tree forcing P in Jech–Shelah's paper, definitions (2)–(4), pp. 749–750, and its rigid regular-open completion A_0. Fix exactly those definitions, rather than merely an unspecified rigid algebra. The natural-number sequences, the indexed master tree and the class of its qualifying subtrees have finite first-order set-theoretic definitions with no set parameters. Restricting a condition to the nodes comparable with one of its nodes remains a condition, as stated after (8), p. 750. Rigidity of the completion is the paper's theorem.

**A canonical countable splitting family.** For n,m∈ω let U_(n,m) be the downward-open set of conditions T such that every node s∈T with length(s)>n has s(n)=m. Put g_(n,m)=ro(U_(n,m)) in A_0, where ro is regularization in the order topology. For an open U this is the set of p such that every q≤p has an r≤q in U, a finite first-order definition over the poset. For fixed n the g_(n,m) are pairwise disjoint and their join is 1: extending the trunk past n decides that coordinate, and different values cannot occur in a common extension.

For every ground sequence z∈ω^ω,

    meet_n g_(n,z(n)) = 0.

Indeed, below any condition there is a restriction whose trunk disagrees with z: conditions are perfect, and restriction to a node remains a condition. These restrictions form a dense set disjoint from the purported meet. This is a statement about the actual regular-open algebra, not an assumption that a generic filter exists in the construction universe.

Consequently every nonzero x∈A_0 is split by some g_(n,m). Otherwise x would settle every member of every displayed partition. Distributivity of a finite meet over an arbitrary join gives, for each n, a unique m with x≤g_(n,m). These choices form a ground sequence z, and x≤meet_n g_(n,z(n))=0, a contradiction. The identity used is `x∧join_i y_i = join_i(x∧y_i)`, valid in every complete Boolean algebra; no stronger lattice distributivity is assumed.

Enumerate the pairs (n,m) in the fixed elementary pairing order on ω, giving g_0,g_1,… . For x>0, choose the LEAST k with `0<x∧g_k<x`. This determines a unique proper part by a finite formula using the standard natural order. It does not well-order A_0.

**Why the whole canonical construction fits in the code.** Now work in ambient ZFC and put B=2×A_0 and κ=|B|. Repeat the full Boolean-valued model and HCode of §§2–3, with full ambient function spaces. A_0 is an infinite complete atomless algebra, so |A_0|≥2^aleph_0: take a countably infinite disjoint family and the distinct joins of its subfamilies. P is a set of trees on a countable master tree, so |P|≤2^aleph_0≤κ. It follows that every subset of P, every tree used in its definition, and every regular-open element belongs to H_(κ+). The set A_0 itself has cardinality at most κ and hereditary size at most κ, so it too belongs to H_(κ+), as do its operation graphs, B's finite-product code, and the sequence (0,g_k).

The definitions of P, its regular-open completion and that sequence are absolute between H_(κ+) and the universe. All natural numbers and trees on the master tree are present; all subsets of P needed by the regular-open definition are present; and the resulting collection A_0 is itself present. One does not require the entire powerset of P to be an ELEMENT of H_(κ+). Quantification over its individual subsets, and the existence of the particular set A_0, suffice. Thus a single fixed first-order formula JSCode(c,G), translated through E, uniquely describes the actual Boolean-algebra code B_0=2×A_0 and its sequence G(k)=(0,g_k).

**Finite pure selection.** In the present model B is rigid, as in §2. For any HCode E, the coded B_0 therefore has exactly one isomorphism h from the actual B. Define a formula Sel(p,q) by saying:

* `p≠0` and `p≤b`, where b is the pure term from §5;
* there exist E^{UUt}, c^U, G^U and h^{tU} with HCode(E), JSCode_E(c,G), and Iso_E(c,h);
* for some coded natural k, k is the least index such that G(k) splits h(p), and h(q) is the meet of h(p) with G(k) in the coded algebra.

All references to G's values, the natural order and the coded meet are ordinary first-order formulas in E. There is no additional function symbol. Minimality binds one more variable of type U and restricts it to the coded ω. This is a finite pure formula with only p,q free. The same type inventory as §4 suffices, and every test is crisp in the full Boolean-valued model.

Every valid E collapses to the same H_(κ+), JSCode picks the same concrete set-theoretic code, and rigidity makes h unique after collapse. The least k and the resulting q are therefore independent of the chosen presentation E. For every nonzero p≤b_0 there is exactly one such q, and it is a nonzero proper part of p. Define

    F_JS := λp^t. ∃q^t(Sel(p,q) ∧ q).

The join interpreting this existential is exactly its uniquely selected q, just as in §5. Hence Split_b(F_JS) has value 1_B and the closed pure `Q_JS := b∧Split_b(F_JS)` has value b_0≠0. Section 1 forces Q_JS=0 under Atomicity_t, while pure Max(C) asserts Q_JS≠0. This is the same proposed inconsistency conclusion with a different finite selector, in an ambient-full ZFC model. It removes the L-order/condensation input from the decisive argument, at the cost of using the concrete rigid tree forcing and its explicitly defined branch-coordinate family.

The selected q need not be actually true; the existential is used to assemble its Boolean VALUE. Crisp uniqueness is precisely what makes this assembly equal q, including when q is false at the designated evaluation. A mere existentially available, unnamed splitter would not suffice for pure Max; the formulas above specify a closed pure operator.

**End-of-pass audit.** No unresolved mathematical step was identified in the self-audit of the direct route. The particular checks were: full crisp subset quantification in HCode; its two cardinal bounds and Mostowski collapse; presence of all trees and all subsets of P in H_(κ+); presentation independence from rigidity; existence of a least splitting coordinate for every positive element; assembly of a false-at-actuality but nonzero selected proposition; and the use of a false closed IDENTITY, not merely a non-designated Boolean sentence, to establish the pure Max side condition. This remains labeled a proposed proof because it has not been independently checked. Validation of the bundle checks record consistency only; it is not a mathematical verification of this new argument.
