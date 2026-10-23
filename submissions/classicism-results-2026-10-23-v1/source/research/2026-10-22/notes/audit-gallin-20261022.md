# Independent audit: the finite-support Gallin model

22 October 2026. Mathematical audit and additional proofs by the Gallin-audit agent. No human verification, Lean verification, database edits, or literature-novelty claim is asserted. The audited construction is §12 of `/tmp/classicism-research/gallin-comparison.md` as read on this date. The fixed framework is the bundle's C, with e,t and arrows whose codomain is not e; optional assumptions below are additions to C.

## Verdicts

- **PASS:** the displayed finite-support domains form a sound model of H and C, including the original H-theoremhood side condition on Logical Equivalence.
- **PASS:** C5 and all-type Atomicity hold at every world.
- **PASS:** the two original quantified Frege Infinity axioms hold, not merely their finite-n schemata. In fact the same assertion holds at every admitted counting type, and all Frege number domains are externally standard.
- **PASS:** Functional Choice fails already at input/output type (t,t), at every world; the pair-selector argument has no hidden appeal to external fullness.
- **DETAIL SUPPLIED:** the C hierarchy is the exact reduct of an explicit extensional general/Henkin Gallin hierarchy with all Gallin arrow types. It is not a full Gallin hierarchy.
- **STRENGTHENING:** all-type □Intensional Choice holds in this particular model. Relational Choice and ordinary countable choice nevertheless fail, with explicit witnesses below.
- **STRENGTHENING:** the entire Gallin subhierarchy over E and Boolean truth values, without the world base type, is externally full. Thus the choice separation survives full standard finite-type arithmetic, including full second-order arithmetic.
- **STRENGTHENING:** the world atoms and the proposition domain are Frege-infinite but internally Dedekind-finite. An internally countable family of propositions has an externally finite actual extension.

The original §12 proof has no substantive gap found. Its short closure argument and its use of the word “Gallin” benefit from the explicit details in §§1–3 below. The construction and proofs use only ZF; in particular their validity in ZFC does not rely on assuming any failure of metatheoretic Choice.

## 1. Exact domains, supports, and the genuine Gallin expansion

Let A be a countably infinite set, let W=A, and let G=Sym(A). Take a separate individual sort E=N on which G acts trivially. A finite set S⊆A supports an element x of a G-set when every g fixing S pointwise fixes x. All supports in this note are subsets of A, not sets of individuals.

Set D_e=E. Set D_t to the finite/cofinite subsets of A, with g·p=g[p]. These are exactly the finitely supported subsets of A: outside a support S all points are interchangeable, so membership must be constant there. Conversely a finite set, or its finite complement, is a support.

For every admitted C arrow σ→τ define

    D_(σ→τ)={f:D_σ→D_τ : f has a finite support},
    (g·f)(x)=g·f(g^(-1)·x).

If S supports f then g[S] supports g·f, so these domains really are G-sets. Every domain is nonempty: use 0 at e, ∅ at t, and constant functions inductively. A constant function with value b is supported by any support for b. All elements of all domains have finite support by construction.

For the full Gallin expansion, use base sorts E, W=A, and o={0,1}, with the indicated actions (trivial on E,o). At **every** simple Gallin arrow α→β, including arrows returning E or W, take all finitely supported set-theoretic functions between the previously constructed domains, under the same conjugation action. The W→o domain is exactly the finite/cofinite subsets of W, via characteristic functions. Induction on C types shows that the expansion's domains at

    e*=E, t*=W→o, (σ→τ)*=σ*→τ*

are exactly the domains above. Thus no unproved reverse-representation theorem is needed to call this an extensional general Gallin model. It is nonfull: already W→o omits every infinite coinfinite subset of A.

A useful currying lemma will be used repeatedly. If h:X×Y→Z has support S, then h(x,-) has support S∪supp(x), and x↦h(x,-) has support S. Hence finitely supported multivariable relations give admitted curried functions. This handles all tuple notation without silently using a product type in C.

## 2. Logic, quantifiers, λ-closure, and Logical Equivalence

At evaluation world w, p:t is true exactly when w∈p. Boolean operations are ordinary Boolean set operations. Equality at every type has value W when the two semantic objects are equal and ∅ otherwise. Its curried equality function is equivariant. Therefore the C definition □p:=(p=top) says exactly that p=W.

For F∈D_(σt), define

    All_σ(F)=⋂{F(x):x∈D_σ}.

If S supports F and g fixes S, then

    g[All_σ(F)]=⋂_x g[F(x)]=⋂_x F(gx)=All_σ(F).

The permutation x↦gx is a bijection of D_σ. Thus the intersection is finitely supported and belongs to D_t; no closure of D_t under arbitrary **external** intersections is being presumed. The calculation with arbitrary g also gives All_σ(gF)=g All_σ(F), so the quantifier operation itself has empty support and is admitted at type (σt)t. Existential quantification is dual. The same argument in the expanded hierarchy establishes the ordinary Gallin o-valued quantifiers at every Gallin type.

Application is equivariant by definition. Every logical constant is equivariant. Inductively, for each term u and valuation ρ,

    [[u]]_(gρ)=g·[[u]]_ρ.

For λx.u, fix the values of its finitely many remaining free parameters, and let S be the union of their finite supports. If g fixes S, equivariance gives

    [[u]]_(ρ[x:=gx])=g·[[u]]_(ρ[x:=x]).

This is exactly the assertion that the denoted function has support S. Each value belongs to the codomain by the induction hypothesis; hence the entire function is admitted. Bound arguments do not require one common global support: their supports vary with the argument, as the conjugation equation allows. This proves full λ-closure with parameters and the usual β-laws. It also establishes the ordinary general-model truth clauses for the extensional Gallin language and, by the displayed translation, H soundness in the original C reduct.

Finally suppose the matrices A,B of a Logical Equivalence instance are H-equivalent. H soundness makes A and B have the same truth value at every world under every assignment. Their denoted propositions are therefore equal subsets of W. Their λ-abstractions are equal set-theoretic functions at every argument tuple. The C identity asserted by Logical Equivalence thus has value W. This uses H-theoremhood precisely where required; it does not replace it by equivalence from optional hypotheses.

## 3. C5, Atomicity, and useful positive consequences

Equality and inequality are W/∅-valued at every type, so □ND holds.

At any relational type τ=σ_1…σ_n t, a nonbottom F has a tuple a and w∈F[a]. Define H[b]={w} when b=a and H[b]=∅ otherwise. Its support is contained in {w}∪⋃_i supp(a_i), by the currying lemma. It is admitted, is nonzero, and is below F in the actual algebraic order. Any nonzero K≤H has the unique same world/tuple point, so K=H. Thus H is an atom. The n=0 case is precisely the singleton {w} proposition. Atomicity therefore holds at all relational types and every evaluation point.

The following direct constructions are useful checks on the recorded C5+Atomicity consequences.

1. **Actuality:** {w} is the unique true propositional atom at w.
2. **Gallin comprehension:** for F with support S, freeze its w-extension by R[b]=W iff w∈F[b], and ∅ otherwise. R has support S∪{w}, is admitted, is coextensive with F at w, and both R and its complement are persistent.
3. **Boolean Completeness:** if X:τ→t is supported by S, let A_w={F∈D_τ:w∈X(F)}. Its pointwise meet H[b]=⋂_(F∈A_w)F[b] is supported by S∪{w}, by the same simultaneous action argument as in §2, and is the genuine greatest lower bound of the selected family. Thus internal completeness holds although D_t is externally incomplete.
4. **Plenitude:** if U:σ→τ→t is actually total and single-valued at w, the unique output function f(x) is supported by supp(U)∪{w}; uniqueness forces the conjugation equation. Hence f is admitted when τ≠e. Arbitrary choice never enters this argument.

All these verifications hold at every world, hence verify their boxed forms where those forms are in the original language. No theorem is boxed merely because it was proved under an optional hypothesis.

A narrow proved-only `Engine` query with premises C5, Atomicity, AI_e, AI_t, □Intensional Choice confirmed the recorded implications to □Plenitude, □Boolean Completeness, □Rigid Comprehension, □Gallin Extensional Comprehension, and Transversal. It found no recorded entailment, exclusion, or countermodel for Functional Choice or Relational Choice from that full package. The new countermodel proofs below fill that evidential gap for this package; absence from the engine was not used as a mathematical argument.

## 4. Frege standardness and all-type quantified Infinity

Fix any admitted counting type σ and put ν_σ=(σt)t. Let z_0 be the bundle's zero cardinality and z_(n+1)=Suc(z_n). The operators zero and successor are pure semantic objects, hence equivariant; each z_n therefore has empty support. The external set N_σ={z_n:n∈N} is invariant, so its rigid characteristic predicate

    Q(Z)=W if Z∈N_σ, and ∅ otherwise

is admitted at type ν_σ t. It contains zero and is closed under successor. Consequently any object satisfying the impredicative FiniteCardinality predicate at any world belongs to N_σ. Conversely, every actually inductive predicate contains each z_n by ordinary external finite induction. Thus the extension of FiniteCardinality_σ at every world is **exactly** N_σ.

Induction on n using the source's successor-removal definition proves

    w∈z_n(X) iff {x∈D_σ:w∈X(x)} has exactly n elements.

The successor step removes one actual member, and equality is genuine identity. Every finite subset of D_σ has an admitted rigid characteristic predicate: take the finite union of supports of its members. Every D_σ is infinite (e and t are infinite; constants inject an infinite codomain into every arrow domain). Therefore z_m≠z_n for m≠n, and no z_n holds of the universal property at σ. This proves the quantified Frege Infinity axiom at every σ, including the original AI_e and AI_t, at every world.

For completeness, the recorded Sum and Prod definitions also give ordinary arithmetic, not merely an abstract Peano theory. For Sum(z_m,z_n,z_o), induction forces every admitted successor-closed relation containing (z_0,z_m) to contain (z_n,z_(m+n)). Conversely the rigid characteristic relation {(z_i,z_(m+i)):i∈N} is equivariant and admitted, and excludes all wrong output pairs. The analogous admitted relation {(z_i,z_(mi)):i∈N}, using the already verified Sum, verifies Prod. Hence all first-order arithmetical sentences have their standard truth values at every world and every counting type.

In the all-Gallin-types expansion there is a still stronger fact. Every type generated solely from E and o has trivial G-action. At a base this is stipulated; if both component domains have trivial action, every function between them is fixed, so the finite-support restriction omits **no function**. By induction that entire subhierarchy is externally full. In particular, ordinary subsets of N, relations on N, and their higher-order collections are all present. In the original C reduct the rigid E-properties include every subset of E: X_B(n)=W iff n∈B. Collections of these rigid codes, and further iterated collections, have equally equivariant characteristic predicates. Thus the full ordinary mathematical sector is visible through rigid coding even though the original t is a world-intension type.

## 5. Functional and Relational Choice fail

Let Atom(p) mean the bundle's Boolean atomhood predicate at t. In this model its instances are exactly the singleton subsets of A. Let Pair(p) mean that p is the union of two distinct atoms. Define the pure admitted relation

    U(p,q) := (Pair(p) ∧ Atom(q) ∧ q≤p)
              ∨ (¬Pair(p) ∧ q=top).

All its component relations are rigid and equivariant. U is serial at every world. If an admitted operation f:t→t selected U, take a finite support S for f and distinct a,b∉S. Then f({a,b}) must be {a} or {b}. The transposition (a b) fixes S and its input but swaps both eligible outputs, contradicting the conjugation equation. Therefore the (t,t) Functional Choice instance fails at every world.

For a selecting functional **relation** V:t→t→t at a fixed evaluation point w, enlarge its finite support to contain w. Choose a,b outside that support. The same transposition fixes the truth of V at w and fixes its input {a,b}, while exchanging the two eligible outputs. Existence and uniqueness at w are incompatible. Hence the corresponding Relational Choice instance fails at every world as well. Adding the evaluation point to the support is essential in this relational version; without it, invariant denotation alone would not justify invariant actual truth.

Consequently Transversal Choice also fails by its recorded implication to Relational Choice, whereas the narrower coextension-class Transversal principle holds by Actuality. This is consistent with their exact different definitions.

## 6. New: all-type Intensional Choice holds

Here the exact original definition matters. For F:σ→t, Intensional Choice says that if every world has an F-instance, there is an admitted G≤F with exactly one instance at **each** world. It does not demand one fixed entity that works at every world.

Let S support F and suppose ∀w∈A ∃x∈D_σ with w∈F(x). Choose a∉S and one witness x at a. Choose a finite support T for x and put

    B=(S∪T)\{a}.

Then a∉B, S⊆B, and B∪{a} supports x. For each w∉B choose any permutation g fixing B pointwise with g(a)=w, and define h(w)=g·x. This value is independent of the chosen g: if g_1(a)=g_2(a)=w, then g_2^(-1)g_1 fixes B∪{a} and thus fixes x. Since g fixes S and a∈F(x), equivariance gives w∈F(h(w)). Moreover the map on A\B is equivariant under every permutation fixing B.

For each of the finitely many b∈B choose a witness x_b with b∈F(x_b), and set h(b)=x_b. Choose finite supports T_b for these finitely many objects. Then

    K=B∪⋃_(b∈B)T_b

supports the total map h:A→D_σ: a permutation fixing K fixes every exceptional b and x_b, and on A\B it respects the equivariance just proved. Only finite choice was used.

Now define G(y)={w:h(w)=y}. For each y, K∪supp(y) supports this subset of A, so G(y)∈D_t. The curried graph G itself has support K and lies in D_(σt). At every world it has exactly one instance, namely h(w), and its pointwise subset relation G≤F is immediate. This is precisely the requested Intensional Choice witness. The argument works also when σ=e; it never uses a forbidden original C operation returning an individual. We used h only in the metatheory and then represented its allowed graph G.

The proof works for every F and independently of the designated evaluation world, so **all-type □Intensional Choice holds**. Combined with §5 it proves the strict consistency separation

    C5 + Atomicity + AI_e + AI_t + □Intensional Choice
    + ¬FunctionalChoice_(t,t) + ¬RelationalChoice_(t,t).

All source arithmetic and the full E/o sector of §4 may be retained. Thus even this strengthened positive package does not imply ordinary Functional or Relational Choice.

## 7. New: countable choice fails despite standard arithmetic

Fix counting type t and write ν=(tt)t, Num(n)=FiniteCardinality_t(n), and A_p=λa^t(Atom(a)∧a≤p). Define

    V(n,p) := (Num(n) ∧ n(A_p)) ∨ (¬Num(n) ∧ p=top).

This is an admitted pure equivariant rigid relation of type ν t t. At n=z_k, its eligible outputs are exactly the k-element subsets of A: a finite p has exactly |p| atoms below it, whereas a cofinite p has infinitely many. Thus every n has an eligible output, using the fallback top on nonnumbers.

If f:ν→t selected V and S supported f, each z_k is fixed by every g, so f(z_k) must be fixed by Fix(S). A proposition fixed by Fix(S) is either a subset of S or the complement of a subset of S. The cofinite options have infinitely many atoms. The finite options have at most |S| atoms. Taking k>|S| contradicts the selection condition. Therefore even this numerically indexed family has no operation selecting outputs.

Its restriction to Num is an internally countable family: the identity graph injects its index field into itself. A selecting functional relation at an actual world likewise fails: enlarge its support by that world, use uniqueness to force the selected p to be fixed by its stabilizer, and repeat the cardinality bound. This is an explicit failure of countable choice, not just a possible consequence of general Choice failing. There is no extra countable-choice principle record assumed here.

## 8. New: finite fixed sets, Dedekind-finiteness, and internal countability

For any finite S⊆A,

    (D_t)^Fix(S) = P(S) ∪ {A\B:B⊆S},

which has exactly 2^(|S|+1) elements. In particular every finitely supported map from an empty-support number field N_σ to D_t has finite range. There is no supported injection N_σ→D_t or N_σ→{world atoms}.

There is also no admitted graph injecting all atoms into N_σ, even just at one actual world w. If its support together with {w} is K, take distinct a,b outside K and the transposition swapping them. Number values are fixed; the alleged actual label of {a} is also a label of {b}, contradicting injectivity.

The proposition domain is internally Dedekind-finite even in the operational sense available at type t. If f:t→t were an admitted injective nonsurjection, choose p outside its range. The sequence p,f(p),f²(p),… is externally pairwise distinct, while every term is supported by the one finite set supp(f)∪supp(p). This contradicts finiteness of the displayed fixed-point set. The same proof applies to an admitted injection on the atom field. Actual functional-graph formulations reduce to supported maps by uniqueness and adding the evaluation point to the support.

Nevertheless both domains are Frege-infinite: D_t by §4, and the atom field because its actual extension has externally infinitely many members and no standard numeral counts it. This is the familiar distinction between finite-cardinality Infinity and Dedekind Infinity in a setting without the relevant Choice, here demonstrated in the exact source language wherever the types permit its formulation.

Finally let X:t→t have actual extension B at w and satisfy the source's Ctbl_(σ,t)(X) definition, witnessed by R:t→ν_σ→t. Let K contain supports of X,R and w. For any p∈B and g fixing K, gp∈B. The reflexive case y=z=p of Ctbl supplies a standard numeral n with R(p,n) true at w. Equivariance, g(w)=w, and g(n)=n imply R(gp,n) true at w. The injectivity clause of Ctbl then gives gp=p. Thus every p∈B lies in the finite fixed set (D_t)^Fix(K), so B is externally finite. Conversely, any finite actual family has a finitely supported graph labeling its distinct members by distinct standard numerals. Therefore, at every point, an admitted family of propositions is internally countable iff its actual extension is externally finite.

The external countability of A and D_t does not supply an admitted enumeration. This is exactly where confusing ambient ZFC countability with internal countability would invalidate an argument.

## 9. Source and validation boundaries

The source definitions checked were `topic.yaml`, the Framework/Notation/Frege sections of `background.md`, and the exact records for C5, Atomicity, Functional Choice, Relational Choice, Intensional Choice, Plenitude, both quantified Infinity axioms, Countable Boolean Completeness, Actuality, Strong Actuality, and the two Transversal principles. The existing finite-support-permutations/action model is not identified with this construction: its world action and higher-domain construction differ. Existing choiceless Henkin records are background comparisons, not the direct source of these proofs.

The original construction belongs to the research note being audited. Sections 1–8 above supply independent detailed checking and additional deductions. Any future database entry for these additional arguments should cite this original argument as `misc`, preserve actual authorship/status, and not claim a named human checked it. No main-database files or Lean files have been changed.

## 10. Precise full-core interpretation and Choice inside that core

There is a full ordinary simple-type hierarchy **interpreted** in the original C model, without treating the original all-domain quantifiers as if they already ranged over the core. Define fields H_σ⊆D_σ recursively by H_e=E, H_t={∅,W}, and the following arrow coding. For every external function f:H_σ→H_τ, let its code f^+:D_σ→D_τ agree with f on H_σ and take the fixed core value bottom_τ off H_σ. Set H_(στ) to the collection of these codes. All original arrow codomains τ are relational, so bottom_τ exists and belongs to the core, by induction.

Every member of every H_σ is individually fixed by G. At an arrow, G fixes its core inputs and outputs, and preserves the core field; outside that field the extension is constant. Thus every external f has an admitted empty-supported code. The field predicate Core_σ(x), true exactly on H_σ, is also admitted and rigid. Restriction gives a bijection H_(στ)≅(H_τ)^(H_σ). Application on core arguments is preserved. Core λ-abstraction uses the default extension, and core quantifiers are the original quantifiers relativized to Core_σ. Equality, Boolean truth values, and these relativized quantifiers have their ordinary meanings. Therefore every sentence true in the standard full simple-type hierarchy over E=N and {0,1} remains true in this interpreted core.

This is an interpreted subhierarchy, not the assertion that H is an elementary submodel or is closed under the original unrestricted quantifier operations. That distinction prevents a false identification of the original proposition sort D_t with its two-element core H_t.

**ZFC core-choice theorem.** Let U:σ→τ→t be any admitted, possibly intensional relation, and fix a world w. Suppose for every x∈H_σ there is y∈H_τ with w∈U(x,y). In ZFC choose an external selector f:H_σ→H_τ. Its default-extension code f^+ belongs to H_(στ), hence to D_(στ), and selects U for every core input at w. Thus Functional Choice restricted to core inputs/outputs holds whenever τ≠e. For output e, the rigid graph of the selector is admitted and gives the corresponding Relational Choice statement. This uses metatheoretic AC and is asserted in ZFC; the earlier construction and separation proofs need only ZF.

Consequently the failure in §§5 and 7 persists while ordinary full-core Choice holds. Neither the missing world selectors nor the failure of numerical choice into world-dependent propositions can be repaired merely by strengthening ordinary number/set comprehension within the core.

## 11. Audit of the effective atomic-world representation proposal

The parent proposed combining §§13–14 of `/tmp/classicism-research/rigidity-actualization.md` with the auxiliary H_0 presentation of `/tmp/classicism-research/positive-effective.md`. The intended hypothesis is a **countable adequate original B-model code**: numbered sorted domains, decidable equality, uniform denotation of every finite original term under arbitrary finite assignments of named parameters, and actual truth. Domain membership is included in the code. This is stronger than a bare atomic diagram of an applicative reduct.

**PASS with a numbering clarification.** The internal rigid-core representation gives an effective auxiliary H_0 representation, and a degree-preserving version follows when the numberings are chosen as below. No transformation for arbitrary bare category/action codes follows.

For each auxiliary type α, its ambient original type c(α) and rigid field predicate H_α are obtained by effective finite recursion on α. Bases are all e-objects, propositional atoms, and {bottom,top}; arrows are rigid relations supported on the earlier fields. Source membership in H_α is decided by evaluating its original formula at the named source object. Source term evaluation computes restricted application. The distinguished auxiliary world is found by searching source t-codes for the unique true atom, testing `Atom(a) ∧ a`; existence and uniqueness are consequences of B. Every auxiliary first-order formula with parameters translates effectively to an original formula, with quantifiers restricted to the relevant H_α predicates. Therefore its truth is computable in the source term-and-truth code. Intrinsic rigid comprehension in the cited §13 supplies every H_0 comprehension instance, including formulas quantifying over other auxiliary sorts; no external full powerset is used.

There is a subtle difference between reconstructing an isomorphic source copy and recovering the **given numbered source code**. If all auxiliary sorts are simply numbered by their ambient core-object numbers, inverse translation gives an isomorphic source copy; that alone does not prove Turing equivalence with the original numbered presentation, since a noncomputable relabeling can change a presentation's degree.

To obtain the exact degree statement, number every auxiliary sort in the syntactic image T(σ) of the original type translation by the original D_σ numbers, using j_σ to identify those numbers with the corresponding core objects. The type translation is injective, and its syntactic image is decidable: e is in the image, s→o represents t, and translated arrows can be parsed recursively; the bases s,o themselves are not original-type images. Number other auxiliary sorts by tagged ambient-core numbers. On an input/output in a translated sort, use j_σ/k_σ to pass between the chosen source numbering and the actual core object. These maps are effectively evaluable original terms at relational types and the identity substitution at e. Thus all auxiliary operations, field membership, and the complete auxiliary elementary diagram remain computable in the original code.

Conversely, from that complete auxiliary diagram, interpret each original type σ as the already identically numbered sort T(σ). Translate an original finite term to its auxiliary value formula. Comprehension and extensionality guarantee a unique value; search the target sort and ask the diagram whether the value formula holds. This uniformly recovers original term denotations under arbitrary named assignments. Recover original truth by evaluating the translated proposition at the named actual world; equality is auxiliary equality. Domain-membership queries recover the same source domain codes. Hence this inverse recovers the original operational code, giving genuine Turing equivalence for these specified numberings.

The requirement of parameterized interpretation is material: closed-term evaluation alone does not decide arbitrary field-membership instances or auxiliary formulas with non-denotable parameters. The requirement of a full elementary auxiliary diagram is likewise material: a bare atomic diagram need not decide the universal formulas defining quantifiers or the unique-value search for λ-abstractions. The theorem concerns adequate model representations, not all conventional reduct codes, and it does not assert external fullness.
