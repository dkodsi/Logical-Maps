# Complete finite coalescences with individual expansion

22 October 2026. Original mathematical argument developed by the construction and local-strengthening research subagents. No human check, Lean verification, or repository-record update claimed. Direct source of the new results: misc, this note.

This continues `/tmp/classicism-research/finite-base-barcan-chain-20261022.md`. The standing logic, action-model semantics, Intensionality, NI, and pure/signature conventions are unchanged.

## 1. Exact pure formulas and claims

Let F be the Fregean Axiom and A_n := F and E_n^e, for an external positive integer n. Define the single closed pure sentence

    L_n := E_1^e and E_4^t and BF_t and
           exists p^t [p and Atom_t(p)
                        and Box(p)=bottom
                        and Box(not p)=not p
                        and Box(p -> E_1^e)
                        and Box(not p -> A_n)].               (1)

Here all displayed parameters other than bound variables are pure defined terms, and BF_t is the single predicate-form sentence. The boxes in (1) are explicit assumptions, not consequences obtained by necessitating optional assumptions.

Put

    C_n := L_n and E_(2^(n+1))^(et).                          (2)

The exponent and cardinality index in (2) are external finite numbers, so (2) is an ordinary finite sentence.

**Results.**

1. Every L_n world has finite domains at every type. Its domains have the form arbitrary actual extensions paired with allowed relational profiles in a full n-individual Fregean target.
2. L_2 alone forces all such profiles to be allowed. It is consistent and pointed-complete over C.
3. C_n is consistent and pointed-complete for every n. It isolates the full coalescence of a singleton root with a full Fregean n-individual leaf.
4. For n>=2, C proves L_n -> not BF_e. Thus these are complete finite cells that fail BF at type e while retaining BF_t.
5. L_3 alone is not complete: there are two models with exactly the same displayed base data but respectively 8 and 16 root unary predicates. This is an explicit obstruction to dropping the profile fullness requirement in general.

Pointed-complete means that every pure formula P(x), with no free variable other than the displayed individual variable, has one fixed truth value in all worlds satisfying the cell, for every interpretation of x. Since the actual individual domain is singleton, ordinary and pointed completeness coincide here.

## 2. Root-like and leaf-like targets

Fix an L_n world o and a witness p. Write b=not p. Its propositional Boolean algebra is B={bottom,p,b,top}, with Box p=bottom and Box b=b. Actual truth selects p.

As in the preceding note, finite D_t(o) plus BF_t makes every transport h:o→v surjective at t. The target truth of h(p) determines two cases.

If h(p) is true, h(p) cannot be top: otherwise naturality of Box would give top=Box(h(p))=h(Box p)=bottom. Both h(p) and h(b) are therefore nonzero. The Boolean map from B is injective, and surjectivity makes it an isomorphism onto a four-element target algebra. It preserves actual truth: every source proposition is one of bottom,p,b,top, and p is true at both ends. Call v root-like along h. The boxed p-condition gives E_1^e there.

If h(p) is false, h(b) is true. Since h(Box b)=h(b), the target satisfies Box(h(b)); by the definition of Box, h(b)=top and h(p)=bottom. Its entire propositional domain is then the two-element image of B. The boxed b-condition gives A_n there. Call v leaf-like along h. This target is a full finite extensional typed structure on n individuals.

The classification is exhaustive. There is at least one leaf-like arrow because b is nonbottom, hence possible, while b is currently false. All leaf projections on source propositions are the same truth map: they send bottom,p to bottom and b,top to top.

At every root-like arrow, the truth of **every source proposition** is preserved. Consequently the truth of every formula with source parameters, including quantified formulas, is preserved. This observation does not require the corresponding higher-type transport to be surjective.

Choose one leaf arrow h:o→v for the remainder of the reconstruction. Let a be the root's unique individual, and a_v=h(a) its marked leaf individual.

## 3. Each relation is determined by its actual extension and one leaf value

For a relational type tau=sigma_1...sigma_k t and F in D_tau(o), let S_F be its current truth extension on the product of the current input domains. Consider

    Phi_tau(F) := (S_F, h(F)).                                (3)

We claim Phi_tau is injective.

Suppose Phi_tau(F)=Phi_tau(G). Their current extensions agree, so the source proposition

    Q := forall x_bar, F[x_bar] iff G[x_bar]

is true. At every root-like arrow Q remains true, including its full target quantifiers, by the truth-preservation observation of section 2. Thus the transported relations are coextensive there.

At the chosen leaf, h(F)=h(G). Hence the source proposition delta=(F=G) has true leaf image. All leaf projections on source propositions agree, so delta has true image at every leaf-like arrow. Therefore F and G are identical, and hence coextensive, at each leaf-like target as well.

They are necessarily coextensive at all accessible targets, and C's Intensionality gives F=G. This proves injectivity. It also shows why merely counting current application tables would be insufficient: the second coordinate in (3) can contain information about leaf individuals absent from the root.

Induct on types. The current base domains are finite. If the argument domains of tau are finite, there are only finitely many current extensions S_F, and D_tau(v) is finite because v is a full finite Fregean world. Injectivity of (3) therefore proves D_tau(o) finite. Thus every actual type is finite without assuming BF_e or all-type BF.

## 4. Exact product decomposition and closure of allowed profiles

Let S_tau := h[D_tau(o)] be the allowed leaf profiles at a relational type. In fact the image of (3) is exactly

    P(product_i D_sigma_i(o)) × S_tau.                        (4)

For any desired current extension S, use its finite equality-case formula U_S(x_bar), with the finitely many current argument entities as parameters. Its current extension is exactly S. If F_0 has a desired allowed profile alpha, then

    lambda x_bar,
      (p and U_S(x_bar)) or (b and F_0[x_bar])                (5)

has current extension S, because p is currently true and b false. At the chosen leaf, p is bottom and b top, so its profile is alpha. This proves (4).

The profile family is closed under all admitted term operations evaluated in the full leaf structure, including its full quantifiers: choose preimages of finitely many profile parameters and transport the corresponding root term. It includes the marked individual a_v as an available individual parameter and both propositional values. It can nevertheless omit relational leaf entities: the individual domain of the root still supplies only the single marked individual, and there is no function type with output e.

## 5. Why two leaf individuals force all profiles

In a full two-individual extensional world with a marked individual a_v, every relational entity is denoted by a pure term T(a_v), with no free variable other than that individual variable.

At e-inputs, the two arguments are distinguished by x=a_v and x!=a_v. The latter case contains exactly one individual; no e-valued term naming it is needed. At t there are just bottom and top. Inductively, suppose every relational argument/output entity has a term name and the relevant domains are finite. For a relational input, finite equality cases against those names give all possible tables. For an e-input, the two cases just described do so. Boolean combinations of the output terms and lambda abstraction realize every table at the new relational type. This proves the naming assertion at every type.

Transporting T(a) from the root gives T(a_v), so every relational leaf entity belongs to S_tau. Therefore in (4), S_tau=D_tau(v) at every relational type. This is exactly the full two-world coalescence hierarchy. In particular the root has 2*4=8 unary predicates, so L_2 entails E_8^(et), and the extra conjunct in C_2 is redundant.

## 6. One finite unary-predicate cardinality forces full profiles for any n

For tau=et, the root actual extension has two possibilities and the full leaf has 2^n unary predicates. Formula (4) therefore gives

    |D_et(o)| = 2 |S_et| <= 2^(n+1).

Under the extra conjunct in C_n, equality holds. Since S_et is a subset of the finite full leaf domain, it must be all of it.

Choose root unary predicates R_1,...,R_n whose leaf profiles are the n singleton properties of the leaf individuals. These are finitely many parameters, used in the proof; no new constants occur in C_n. In the leaf structure, each R_i defines a unique individual. Finite case formulas using R_i(x) therefore distinguish every e-input, without an e-valued choice operation. Starting from bottom and top, finite equality cases on named relational inputs and the singleton cases on e-inputs inductively name every relational leaf entity by a term in a_v,R_1,...,R_n. Each such term lifts to the root, so S_tau is full at every relational type.

Hence C_n forces the full hierarchy

    D_tau(o) = P(product_i D_sigma_i(o)) × D_tau(v)

up to the bijection (3). The root individual maps to one marked leaf individual.

This identifies the local logical structure, not only its cardinalities. Application takes the actual fiber and applies the leaf profiles. Equality has actual truth precisely when the two pairs are identical, and leaf truth precisely when their profiles are identical. Thus its proposition is top, b, or bottom as these two tests require. Quantification has its usual actual truth over the actual domain and its usual leaf truth over the full leaf domain. The source proposition domain B identifies a proposition uniquely by these two truth values. Lambda abstraction is determined by its actual extension and leaf interpretation. All logical operations are therefore fixed by this full coalescence representation.

All full n-individual extensional structures with one marked individual are isomorphic. It follows that every pure formula has one fixed actual truth value in all C_n worlds. Completeness for C gives pointed completeness of C+C_n. The same argument applies to L_2 by section 5.

## 7. Explicit models and BF_e failure

For consistency, take two worlds o→v. The root has one individual and v has n individuals; transport maps the root individual to a chosen leaf individual. The leaf is the full extensional n-individual structure. At each root relational type take all pairs

    (arbitrary current extension, arbitrary leaf entity).

Application and transport are as in the ordinary full coalescence construction. Abstraction is closed because every actual extension and every target abstraction are allowed. These models validate C. Propositions are the four subsets of the two-world chain. The root-only proposition p and leaf-only proposition b satisfy the required modal table. Transport at t is onto the two-element leaf domain, so BF_t holds. The boxed cardinality/Fregean conditions in L_n are immediate. There are exactly 2^(n+1) root unary predicates, so C_n holds.

For n>=2, BF_e fails in every L_n world, not merely in this model. Let a be the root's sole individual and X=lambda x, x=a. At the root, forall x Box(Xx) holds, since the only current argument is a. At a leaf-like world there are n individuals and only one is the image of a, so forall x Xx fails. Thus Box(forall x Xx) fails at the root. This is a concrete counterinstance to BF_e.

For n=2 the root and leaf counts begin:

| type | root | leaf |
|---|---:|---:|
| e | 1 | 2 |
| t | 4 | 2 |
| et | 8 | 4 |
| tt | 64 | 4 |
| (et)t | 4096 | 16 |

For example the last root count is 2^8*16=4096. The current unary-predicate domain has 8 entities despite only 4 possible entity-valued tables on the root's single individual, so Functionality_et fails as well. The extra entities record truth at the untransported leaf individual.

## 8. Explicit failure of uniqueness at three leaf individuals

Let the leaf have individuals {a,b,c}, with a the root individual's image. Compare two constructions, both with arbitrary actual extensions at every root relational type.

In the first, allow every relational leaf profile. This is the full coalescence, and it satisfies C_3. Its root unary-predicate domain has 2*8=16 elements.

In the second, allow only leaf profiles fixed by the automorphism swapping b and c while fixing a. At every relational type set

    D_tau(o) = P(product_i D_sigma_i(o)) × Fix_(b c)(D_tau(v)).

The root individual has fixed profile a. The fixed relational profiles are closed under every term operation: the swap is an automorphism of the full leaf structure, so it commutes with application, equality, Boolean operations, abstraction, and full target quantification. With fixed parameter profiles every transported term is fixed. At the root every actual extension is allowed. Therefore the same direct closure proof as for the profile-root construction validates C.

All leaf propositions are fixed, so the root still has exactly four propositions and BF_t holds. The actual and leaf individual counts and all boxed clauses of L_3 are unchanged. Thus both models satisfy exactly the same finite base condition L_3.

Only four unary leaf subsets are fixed: empty, {a}, {b,c}, and {a,b,c}. The second model therefore has 2*4=8 root unary predicates. It satisfies E_8^(et) and refutes E_16^(et); the first satisfies E_16^(et) and refutes E_8^(et). Thus L_3 is not complete, and finite base data with only BF_t do not generally determine the higher hierarchy.

The contrast explains the n=2 boundary: the stabilizer of a marked point in a two-element set is trivial, and the unique other individual is definable by x!=a. At n=3 it can be swapped with another unmarked individual, allowing a proper closed family of relational profiles.

## 9. Scope for Strong Possibility

The separately audited profile-root criterion applies to the pointed-complete cells L_2 and C_n. Consequently Max+Atom_t(L_2) and Max+Atom_t(C_n) are consistent, and pure Strong Possibility entails these atom assertions. The cells themselves entail not BF_e for n>=2.

This supplies complete cells with non-surjective individual transport; it does not by itself give a classification of all complete cells. The restricted-profile example proves an actual nonuniqueness result, rather than treating a missing reconstruction proof as evidence of nonuniqueness.

## 10. Finite definability identifies all allowed profile families

We now classify all L_n worlds, within the precise scope of (1). This is stronger than the examples above but is not a classification of arbitrary complete Classicist theories.

Fix the chosen leaf v and its marked individual a_v. Identify its individual set with {1,...,n}, with a_v=1. Its full typed automorphism group fixing the marker is

    G := Sym({2,...,n}).

Every permutation of the individuals extends uniquely to the full extensional hierarchy, and an automorphism fixing all individuals fixes every higher entity by extensionality. Let S_tau be the allowed profiles from section 4, and define

    H := {g in G: g(alpha)=alpha for every relational tau
                              and every alpha in S_tau}.     (7)

**Finite definability lemma.** For every relational type tau,

    S_tau = Fix_H(D_tau(v)).                                  (8)

The forward inclusion follows from the definition of H. For the converse, because G is finite, there are finitely many allowed profiles alpha_1,...,alpha_m whose common stabilizer in G is H. For each g outside H choose one allowed profile moved by g, and use those finitely many profiles. If H=G, the parameter list may be empty.

Choose a fixed enumeration c_1,...,c_n of the leaf individuals, with c_1=a_v. Every relational entity gamma has a pure term T_gamma(u_1,...,u_n) which denotes gamma when the variables denote this enumeration. This is an elementary induction on type: the u_i name all individual arguments, bottom and top name the propositions, and finite equality case tables name every function at each successive relational type. All output types are relational; no operation returning an individual is introduced.

Let beta be H-fixed, of relational type tau=rho_1...rho_l t. Form the term

    U_beta(a,alpha_1,...,alpha_m) :=
      lambda z_bar, exists u_1...u_n [
        Enum(u_1,...,u_n) and u_1=a
        and conjunction_j (alpha_j=T_alpha_j(u_1,...,u_n))
        and T_beta(u_1,...,u_n)[z_bar]],                       (9)

where Enum is the finite formula saying that the u_i are pairwise distinct and exhaust the individual domain. Every term T_gamma in (9) was fixed using the reference enumeration c_bar. Its equivariance under permutations follows from its purity.

At the leaf, the enumerations satisfying the parameter diagram in (9) are exactly g(c_bar), with g in H: u_1=a fixes the marker, and the displayed identities say that g fixes every alpha_j. For each such enumeration, T_beta denotes g(beta)=beta. The reference enumeration is a witness. Thus (9) denotes beta. Because allowed profiles are closed under all leaf term operations with allowed parameters, beta belongs to S_tau. This proves (8).

There is no assertion that the root individual domain equals the H-fixed leaf individuals. The root has only the one marker; (8) concerns relational types. Formula (9) binds its additional individual variables under leaf quantification and does not require root individuals naming them.

## 11. The fixed-profile models give all local structures

For each subgroup H<=G, construct the two-world model with root individual mapping to 1, full n-individual Fregean leaf, and root domains

    D_tau(o) = P(product_i D_sigma_i(o)) × Fix_H(D_tau(v)).    (10)

Every target proposition is fixed, so the root proposition domain has four elements. The fixed profiles are closed under terms because H acts by automorphisms of the full leaf structure. The direct abstraction/Logical Equivalence verification in section 8 therefore validates C. The model satisfies L_n.

Conversely, sections 3–4 and (8) identify any L_n world with the local typed structure (10) for its subgroup H. This includes all logical operations: actual truth uses the actual extension coordinate, leaf interpretation uses the profile coordinate, and equality, quantifiers, and lambda abstraction are determined as in section 6. No claim that the original action category literally has only two worlds is needed; the local typed logical algebra is the same.

Conjugate subgroups of G yield isomorphic local structures by relabelling the leaf individuals while fixing the marked individual. There are finitely many conjugacy classes because G is finite. The next section supplies explicit finite pure sentences distinguishing these classes, so it also rules out an unnoticed elementary equivalence between nonconjugate cases.

## 12. Explicit finite pure isolators for the subgroup cases

For H<=G, regarded as permutations of {1,...,n} fixing 1, let R have type e...et with n individual arguments. Define the finite pure formula psi_H(R,a) by

    exists u_1...u_n [Enum(u_bar) and u_1=a and
      forall x_1...x_n,
        R[x_1,...,x_n] iff
          disjunction_(g in H) conjunction_(1<=i<=n)
                                  (x_i=u_(g(i)))].           (11)

It says that R is the H-orbit of one exhaustive ordered enumeration starting with a. The subgroup H is a finite external index in the displayed finite disjunction; it is not an object-language group variable.

At an L_n world, A_n is exactly the proposition b=not p as an entity. At root-like targets E_4^t makes F false, while at leaf-like targets A_n is true by assumption. Thus A_n and b agree at every accessible world, and Intensionality identifies them.

Use this pure name for the leaf region to define the closed pure sentence

    kappa_H := exists a^e exists R^(e...et),
                         Box(A_n -> psi_H(R,a)).              (12)

In the fixed-profile model for H'<=G,

    kappa_H holds iff H' <= g H g^(-1) for some g in G.        (13)

Proof: fix the reference enumeration c_bar beginning with the marker, and let R_H be its H-orbit. The stabilizer of R_H under G is exactly H: a permutation sends the orbit H(c_bar) to itself exactly when it belongs to H. The leaf relations satisfying (11) are exactly the conjugate-orbit relations g(R_H); their stabilizers are gHg^(-1). A root R with such profile exists exactly when that profile is H'-fixed, which is the containment in (13). The box in (12) imposes only the leaf condition: A_n is false at root-like targets and true at leaf-like targets. The root actual extension of R is irrelevant and may be chosen arbitrarily. This proves both directions.

Now put

    J_H := L_n and kappa_H
                 and conjunction_(K proper subgroup of H) not kappa_K. (14)

The conjunction is finite. It is enough to use all literal proper subgroups; using representatives where justified is merely a shortening.

By (13), J_H holds in the model for H' exactly when H' is conjugate to H. Indeed kappa_H gives g^(-1)H'g<=H. If this containment were proper, that particular proper subgroup K of H would make kappa_K true, contradicting (14). Conversely, if H' is conjugate to H, it cannot be contained in a conjugate of a proper subgroup of H because the latter has smaller order.

Each J_H is therefore consistent and pointed-complete. Its local typed structure is the fixed-profile model (10) for the conjugacy class of H. Completeness for C converts this semantic uniqueness into the stated syntactic completeness. Choosing one H from each conjugacy class gives a finite disjoint complete decomposition of L_n.

For n=1 or n=2, G is trivial, so L_n itself is complete. For n=3, G has precisely the trivial subgroup and the order-two subgroup, recovering exactly the full-profile and swap-fixed models with 16 and 8 unary predicates. For n=4, the subgroup classes of Sym(3) yield four cases: trivial, a transposition subgroup, a three-cycle subgroup, and Sym(3). The latter two both give eight root unary predicates, so unary-predicate cardinality alone does not distinguish every subgroup case. The finite orbit formulas (11)–(14) do.

## 13. Consequences and limits of the classification

The full-profile cell C_n from (2) selects the trivial subgroup: fullness of unary leaf profiles forces every leaf individual to be fixed, and hence the subgroup to be trivial. The two-individual case is automatically trivial because fixing its marker fixes the other individual.

For every H<=Sym(n-1), the profile-root criterion gives consistency of Max+Atom_t(J_H), and pure Strong Possibility entails Atom_t(J_H). These atom conclusions are compatible with the failure of BF_e entailed by J_H whenever n>=2.

The classified family has a singleton actual individual domain, the specified four-element chain propositional algebra, BF_t, and Fregean n-individual targets in its nonactual region. Other finite modal base algebras, non-Fregean target structures, and arbitrary complete C-extensions are outside this theorem's stated scope.
