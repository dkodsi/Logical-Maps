# Finite C5 signature cells and their pointed isomorphism counts

22 October 2026. Original ordinary mathematical deduction by an OpenAI Codex audit agent, following the audited finite-profile construction. No human checking, formal verification, main-database edits, or literature-novelty claim. No consistency of Strong Possibility is asserted.

## 1. Statement and fixed reference language

Fix positive external integers m,k and a finite signature Σ containing only relational nonlogical constants c_l:σ_l. Every σ_l is an admitted type other than e. Work in the original relational type system and in C(Σ). The signature is fixed throughout the Max/SP side conditions.

Let E_d^σ mean that type σ has exactly the fixed external finite cardinality d. Set

    K:=Box ND_t,
    B_(m,k):=K ∧ E_m^e ∧ E_(2^k)^t.

By `finite-c5-profile-cells-20261022.md`, this is a consistent stable pure sentence, K is equivalent to C5, and every world satisfying it has the full finite function hierarchy over an m-element individual domain and a Boolean proposition algebra with k atoms. Its actual truth map selects one of those Boolean atoms. Every permutation of the m individuals and of the k Boolean atoms extends uniquely to an automorphism of the entire typed logical structure. The alternative boxed base-type formulation in `profile-root-construction-20261022.md` §15 defines the same class: its finite-bijection induction supplies C5, while K stabilizes the displayed finite cardinalities and base distinctness facts.

Choose a standard finite hierarchy H_(m,k), with individual set {1,…,m}, Boolean algebra P({1,…,k}), and all functions at every permitted arrow type. Let

    Ω_Σ(m,k):=product_l H_(m,k),σ_l

be the finite set of all interpretations of the finitely many constants. The product is a singleton for the empty signature. Let

    G_(m,k):=S_(m−1) × S_(k−1)

act by the induced type automorphisms, fixing individual1 and Boolean atom1. The former is the anonymous individual marker used in the profile construction; the latter is the actual truth atom of the finite structure.

**Theorem.** There is one finite Σ-formula Δ_ω(z), with z:e its only free variable, for each orbit ω∈Ω_Σ(m,k)/G_(m,k), such that:

1. Every Δ_ω is consistent and complete for pointed Σ-truth: all Σ-terms T(z):t have one fixed actual truth value at all Δ_ω-points.
2. C(Σ) proves that the Δ_ω(z) form a finite disjoint partition of B_(m,k), including the corresponding identities of proposition entities.
3. One singleton Σ-profile model of Max(C(Σ)) satisfies every sentence ∀z Atom_t(Δ_ω(z)), simultaneously for all positive m,k and all their finite orbit indices. It retains the internal proposition-countability witness of the profile construction.
4. SP_Σ proves every one of those atomhood sentences. Consequently, for each fixed m,k, it forces the Boolean interval below B_(m,k) to contain exactly

       N_Σ(m,k):=|Ω_Σ(m,k)/G_(m,k)|

   atoms.

The exact-number conclusion is an ordinary finite first-order Boolean-algebra sentence for each externally fixed m,k, not an internal claim about a coded sequence of all orbit counts. No cardinality oracle, infinite diagram, infinitary disjunction, or object-language Burnside theorem is used.

## 2. What is classified: individuals, Boolean worlds, and constants

At a B_(m,k)-point, the full finite typed algebra is already fixed up to isomorphism. Its actual truth valuation is a Boolean ultrafilter. Since the proposition algebra is finite, exactly one of its k atoms is true. Calling that the actual atom is a consequence of this finite cell, not an additional Actuality assumption at the profile root or throughout C.

A pointed Σ-structure consists of:

- that full finite typed algebra;
- an interpretation of each named relational constant;
- a selected individual z;
- the selected Boolean truth atom.

Every isomorphism of these structures acts by an individual permutation and a Boolean-atom permutation. Conversely every such pair extends through the full type hierarchy and preserves all logical operations. To compare structures with the two selected elements labelled1, both permutations must fix1. Hence the correct group is S_(m−1)×S_(k−1).

Fixing just the anonymous individual is insufficient when k>1: a constant may have different truth at different Boolean atoms. Fixing just the actual atom is also insufficient: a unary constant may distinguish different individual orbits. The two distinguished coordinates are independent.

For unary individual predicates c_i:et, each interpretation is an r-tuple of binary m×k incidence matrices: entry(i,a,w) is1 iff Boolean atom w lies below c_i(a). A propositional constant is a binary k-vector. In that special case the group action is the familiar row-and-column permutation action with one fixed row and one fixed column. Higher-type constants are finite functions in the full hierarchy and transform by the corresponding recursive conjugations; they need not be forced into a misleading first-order incidence-matrix representation.

## 3. Explicit finite diagrams at every permitted relational type

The isomorphism classification is usable in the original finitary language because every required finite diagram can be written explicitly.

Introduce individual variables x_1,…,x_m and proposition variables a_1,…,a_k. Let Enum(x,a,z) assert:

- z=x_1;
- the x_i are pairwise distinct and exhaust type e;
- the a_j are pairwise distinct Boolean atoms and their join is top;
- a_1 is true.

Under B_(m,k), such enumerations exist for every z. Boolean atomhood and join are the ordinary definable Boolean-algebra notions. The displayed finite cardinalities ensure that the atom list has exactly k entries. Exhaustive finite enumeration needs no Choice principle.

For every standard value d in every finite type H_σ, construct a term t_σ^d(x,a):σ by induction on type. At e use the corresponding x_i. At t use the finite join of exactly those a_j belonging to the Boolean value d; the empty join is bottom. If σ=ατ with τ relational, then d is a function H_α→H_τ. Write τ=ρ_1…ρ_ht. Define t_σ^d by a finite equality-table lambda term:

    λu^α v_1^ρ1 … v_h^ρh.
       OR_(b∈H_α) [ (u=t_α^b(x,a))
                     AND t_τ^(d(b))(x,a)[v_1,…,v_h] ].

The empty output tuple covers τ=t. Every type is permitted because the function's output is relational. No function into e is introduced.

Under B and Enum, equality at every type is crisp: top for equal entities and bottom for distinct entities. The finite-table term therefore has precisely the intended actual function. The earlier finite-cell theorem gives Functionality and all functions at each type, so the terms t_σ^d enumerate the type bijectively. This simultaneously verifies higher-type table names, rather than merely assuming that arbitrary elements have names.

For a labelled tuple d=(d_l)∈Ω_Σ(m,k), put

    Δ_d(z):=B_(m,k) ∧ ∃x_1…x_m a_1…a_k
       [Enum(x,a,z) ∧ AND_l(c_l=t_(σ_l)^(d_l)(x,a))].

Changing labelled tuple d within its G-orbit changes only the bound enumeration, so produces an equivalent formula. Choose one representative for each finite orbit and write its formula as Δ_ω. This is a finite external choice, and no canonical computable choice is needed for the theorem. In fact the finite tables and finite group can be enumerated, so orbit representatives and formulas can be computed for fixed finite input data.

Every Δ_ω is C(Σ)-consistent. Use the full finite Boolean-valued structure, give each c_l the selected d_l, select individual1 as z and atom1 as actual truth. The model validates the same H and Logical Equivalence axioms as the finite-cell construction.

## 4. Pointed completeness and the finite partition

Suppose two pointed C(Σ)-models satisfy Δ_ω. The finite-cell theorem identifies both local typed structures with H_(m,k). Their witnessing enumerations carry the marker to individual1 and the actual atom to Boolean atom1. Their constant interpretations lie in the same G-orbit. The corresponding typed isomorphism therefore preserves all constants, the marker and actual truth. It preserves equality, application, lambda interpretation, Boolean operations and the finite quantifier meets/joins. Every Σ-term T(z) thus has the same actual truth at the two points.

This also covers modal terms: Box is defined by identity with top, and the iterated modal definitions are terms in the same preserved language. No extra condition on arbitrary unmentioned future worlds is needed; the finite-cell theorem already identified the entire local typed logical algebra, including the relevant proposition entities and quantifiers.

At any B-point and for any z, choose the enumerations and read off the finite interpretation tuple d. Hence some Δ_ω(z) holds. If two formulas hold, comparing their enumerations gives an element of G carrying one tuple to the other, so their orbit indices coincide. Outside B every Δ is false. Thus soundness/completeness for C(Σ) yields

    C(Σ)⊢∀z [B_(m,k)↔OR_ω Δ_ω(z)],
    C(Σ)⊢∀z ¬(Δ_ω(z)∧Δ_η(z))       for ω≠η.

These are actual C(Σ)-theorems. They may therefore be necessitated and converted by Intensionality to the proposition identities

    B_(m,k)=JOIN_ω Δ_ω(z),
    Δ_ω(z)∧Δ_η(z)=bottom            for ω≠η.

This theoremhood step matters: mere equivalence under an optional assumption would not itself authorize those identities. Here the antecedent B was included inside every Δ and in the displayed discharged theorem.

## 5. Profile atoms and their SP transfer

Use the audited singleton-root construction with Σ-term profiles T(z), components complete for C(Σ), every component object included, and all permitted component interpretations of the constants. Interpret each relational constant by its own term profile plus an arbitrary actual root extension. No new nonlogical constant is added to the reference signature. Auxiliary variables used to write diagrams are bound.

Let a be the sole root individual. For any root proposition p, its old-component profile is represented by some Σ-term T(z). Pointed completeness of Δ_ω makes T(z) uniformly true or uniformly false at all component points where Δ_ω(z) holds. At every other point Δ_ω is false. Consequently descendant truth separation gives a profile identity

    profile(p∧Δ_ω(a))=profile(Δ_ω(a)) or profile(bottom).

As in the original profile audit, this uses all component objects and arrows: uniform current truth at just a collection of initial objects would not by itself establish entity equality.

The root proposition domain is infinite, already from its pure profiles. Thus B_(m,k), and therefore Δ_ω(a), has actual root truth bit0. The actual bit of p∧Δ_ω(a) is also0. The profile identity is accordingly an identity of the full root proposition entities:

    p∧Δ_ω(a)=Δ_ω(a) or bottom.

The finite consistent Δ_ω component witnesses nonzeroness. Therefore Δ_ω(a) is an atom. The same root works for every orbit and every positive m,k. Since the signature is finite, it has only countably many finite-syntax profiles; the existing freely available root graph still provides the internal countability witness.

The sentence U_ω:=∀z Atom_t(Δ_ω(z)) holds at that singleton root and is thus Max(C(Σ))-consistent. After expanding Boolean order, U_ω is a universal finite Boolean combination of typed identities. Its terms may contain the bound diagram quantifiers; that does not change the identity form of the outer atomhood statement. The audited identity-reflection lemma proves

    C(Σ)⊢Diamond_ne U_ω→U_ω.

Hence the correctly referenced SP_Σ instance yields U_ω.

For any actual a, all the finitely many Δ_ω(a) are now nonzero pairwise-disjoint atoms whose join is B. Every atom below that finite join must meet one part nontrivially, and therefore equals that part. Thus there are exactly N_Σ(m,k) atoms below B. One needs only the standing nonemptiness of e to instantiate a; no named individual constant or Choice principle is silently added.

## 6. External Burnside formula for unary and proposition constants

Suppose Σ has r unary constants c_i:et and s proposition constants b_j:t. For π∈S_(m−1), let π^+ be its extension fixing the distinguished row. For τ∈S_(k−1), let τ^+ extend it by the distinguished column. Write c(η) for the number of permutation cycles, and c(π^+×τ^+) for the number of orbits of the coordinatewise permutation on the m×k set.

A binary matrix is fixed exactly when it is constant on these coordinate orbits. A binary k-vector is fixed exactly when constant on τ^+'s cycles. Burnside's finite orbit-counting identity therefore gives

    N_(r,s)(m,k)
      = 1/[(m−1)!(k−1)!]
        SUM_(π∈S_(m−1),τ∈S_(k−1))
        2^[r·c(π^+×τ^+)+s·c(τ^+)].

Equivalently, if λ partitions m−1 and μ partitions k−1, let λ^+=(1,λ) and μ^+=(1,μ), with repetitions retained as separate cycles. Let z_λ=product_d d^(multiplicity_d)·multiplicity_d!, including z_empty=1. Then

    N_(r,s)(m,k)
      = SUM_(λ⊢m−1,μ⊢k−1)
        2^[r·SUM_(a∈λ^+,b∈μ^+)gcd(a,b)
             +s·length(μ^+)] / (z_λ z_μ).

The gcd appears because the product of a cycle of length a and one of length b has gcd(a,b) orbits. These formulas are external finite mathematics calculating the number of diagram indices. The object theory needs only the finite diagrams and their partition/atomhood proofs.

Checks and useful specializations:

- Empty signature: N_(0,0)(m,k)=1. This is pure SP's Atom(B_(m,k)).
- k=1: put q=2^r. Then N_(r,s)(m,1)=2^s·q·binomial(m+q−2,q−1), recovering `unary-signature-finite-atoms-20261022.md`.
- m=1: put q=2^(r+s). Then N_(r,s)(1,k)=q·binomial(k+q−2,q−1). Each Boolean atom has its r+s-bit color, and one color is selected by actual truth.
- r=0: the last formula holds for every m, with q=2^s, because individual permutations act trivially on propositional constants.
- One unary constant and no proposition constants gives the table below. It is symmetric in m,k because this special case has one binary matrix and one fixed coordinate on each side.

| m \\ k | 1 | 2 | 3 |
|---|---:|---:|---:|
| 1 | 2 | 4 | 6 |
| 2 | 4 | 16 | 40 |
| 3 | 6 | 40 | 168 |

For example m=k=3 averages four fixed-matrix counts: (512+64+64+32)/4=168. This finite arithmetic checks the counting formula, not the semantic atomhood theorem.

## 7. What changes when the signature names individuals

The preceding theorem intentionally uses a relational-only signature. Its anonymous marker is indispensable. If instead a finite Σ has u≥1 individual constants, the audited closed-Σ-profile construction has those constant symbols as its root individuals and needs no extra free marker. Complete *unpointed individual* Σ-diagrams then suffice, while the actual Boolean atom must still be distinguished.

For that variant the orbit set is

    [ {1,…,m}^u × product_l H_(m,k),σ_l ]
       / [S_m×S_(k−1)],

where the product ranges over the relational constants and the group fixes Boolean atom1. The u ordered names are part of the interpretation tuple; their denotations may coincide at finite target points. At the root the symbols are distinct as required by signature Max, and outgoing arrows may identify them. Replacing the earlier Enum condition z=x_1 by the finite equations naming each individual constant gives the corresponding closed diagrams. The closed-profile atom proof and finite partition then give exactly this orbit count under SP_Σ.

The existence of at least one name is what justifies dropping the extra anonymous-marker orbit refinement. Setting u=0 in this last formula generally gives the wrong count for the relational-only construction. With one individual name the formula agrees with the anonymous-marker count by the usual stabilizer correspondence. This variant is an application of the separately audited named-root construction, not an assertion that the two profile constructions have identical root individual domains.

## 8. Limits

The model validates all the displayed atom constraints with signature Max. It does not validate, or prove consistency of, full SP_Σ. All signature references remain exact: adding new constants can split these cells, and no conservativity of one maximalization over another is presumed.

Only finite signatures and finite externally fixed m,k are covered. An infinite signature has no finite full diagram of all its interpretations; the argument does not automatically extend to it. No general finite axiomatization of all pointed-complete C theories is claimed. The complete-cell theorem includes many finite non-Fregean examples, but it does not say every consistently atomic pure sentence has this form.

## 9. Independent agent review

The parent OpenAI Codex research agent independently read this proof and the unary-signature specialization on 22 October 2026 and reported PASS. Its review explicitly checked the recursive higher-type finite tables, the two stabilizers, the universal-identity form of ∀z Atom(Δ_ω(z)) despite bound quantifiers inside Δ, the C(Σ)-theorem status of the partition before necessitation/Intensionality, and the use of an arbitrary actual individual rather than an added name. It also verified the count168 and the named-individual variant's dependence on the separately audited closed-profile construction. This is ordinary agent review, not human checking or formal verification.
