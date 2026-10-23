# Finite rigid leaf coalescences: subgroup classification and complete cells

22 October 2026. Original mathematical argument developed jointly by the construction lane and local-strengthening lane. No human check, Lean verification, or repository-record edit claimed. Direct source of the new classification: misc, this note.

## 1. Precise scope

This unifies the individually audited constructions in `/tmp/classicism-research/finite-base-barcan-chain-20261022.md` and `/tmp/classicism-research/finite-coalescence-bf-e-failure-20261022.md`. It uses the audited finite rigid cell

    B_(n,k) := Box(E_n^e and E_(2^k)^t and ND_e and ND_t),

for external positive integers n,k. The proof that B_(n,k) determines the full finite function hierarchy over an n-element individual set and a k-atom Boolean algebra is in `/tmp/classicism-research/profile-root-construction-20261022.md`, section 15. All type transports within such a region are bijective; equality is crisp at all types; Functionality holds and all functions at every admitted operation type occur. For k>1 this is not Extensionality by actual truth coextension.

The underlying typed algebra, omitting its choice of actual truth ultrafilter, has automorphism group Sym(n)×Sym(k). The two factors permute individuals and Boolean atoms. These automorphisms commute with the logical term operations, including finite quantifiers and Box. Every relational entity is named by a pure term using an enumeration of the individuals and an enumeration of the Boolean atoms. The latter naming assertion follows by finite equality case tables, starting from the Boolean combinations of the named atoms.

Define the pure condition

    Q_(n,k)(p) := p and Atom_t(p)
                   and Box(p)=bottom and Box(not p)=not p
                   and Box(p -> (E_1^e and E_4^t))
                   and Box(not p -> B_(n,k)),

and the closed pure sentence

    L_(n,k) := E_1^e and E_4^t and exists p^t Q_(n,k)(p).      (1)

No BF instance is assumed in (1). All modal conditions needed below are explicitly boxed in the formula.

**Theorem.** The local typed logical structures of L_(n,k) worlds are exactly the fixed-profile coalescences associated with subgroups

    H <= G_0 := Sym(n-1) × Sym(k)

whose action on the k Boolean atoms is transitive. Conjugate subgroups give the same isomorphism class. Each conjugacy class is isolated by an explicit finite closed pure sentence and is pointed-complete over C. Thus L_(n,k) has a finite decomposition into consistent pointed-complete cells.

The scope is the explicitly specified two-region condition (1). The theorem does not classify arbitrary finite or complete Classicist models.

## 2. The two kinds of accessible targets

Fix an L_(n,k) world o with witness p, and write b=not p. The source proposition algebra is {bottom,p,b,top} with actual truth selecting p. For an arrow h:o→v there are two cases.

If h(p) is true, it cannot be top, since naturality would give

    Box(h(p)) = h(Box p) = bottom.

Both h(p) and h(b) are therefore nonzero, so h_t embeds the source four-element Boolean algebra. The boxed p-condition makes the target propositional algebra also four-element; hence h_t is an isomorphism. It preserves actual truth on every source proposition, because p is true at both ends. The target has one individual. Call such a target root-like.

If h(p) is false, h(b) is true, and Box(h(b))=h(b) makes h(b)=top as an entity. Consequently h(p)=bottom and the image of h_t is exactly {bottom,top}. The boxed b-condition makes the target a B_(n,k) world. Call such a target leaf-like.

There is a leaf-like arrow: b is nonbottom, hence possible, while it is currently false. All leaf-like arrows act identically on the four source propositions, sending bottom,p to bottom and b,top to top, even though their target proposition domains have 2^k elements.

At a root-like arrow, the actual truth of every formula with source parameters is preserved. This follows from naturality of its proposition denotation and the truth-preserving isomorphism at t; it does not assume higher-type surjectivity.

Choose a leaf arrow h:o→v, let a be the root's unique individual, and mark a_v=h(a) in the leaf. Identify the individual set of the leaf algebra with {1,...,n}, with a_v=1, and its Boolean atoms with {1,...,k}. Its term-algebra automorphisms fixing the marker form G_0=Sym(n-1)×Sym(k). The group is deliberately not restricted to automorphisms preserving one chosen leaf truth ultrafilter.

## 3. Reconstruction by actual extension and one leaf profile

For a relational type tau=sigma_1...sigma_l t, associate to F at o its actual truth extension S_F and its chosen leaf value h(F):

    Phi_tau(F) := (S_F,h(F)).                                 (2)

This map is injective. If F,G have the same current extension, the source proposition forall x_bar (F[x_bar] iff G[x_bar]) is true. It stays true at every root-like target, including its full target quantifiers. If h(F)=h(G), the source equality proposition (F=G) has top image at the chosen leaf. Since all leaf maps have the same action on the source four propositions, that equality has top image at every leaf-like target. Thus F and G are coextensive at every accessible world; Intensionality gives F=G.

Induction on types now proves every root type finite: the input domains are finite by induction, the actual extension set is finite, and the full rigid leaf domain at tau is finite.

Write S_tau=h[D_tau(o)] for the allowed leaf profiles. Every pair of an arbitrary actual extension and an allowed profile is realized. Given a profile witnessed by F_0 and a desired actual extension S, use the finite current equality-case predicate U_S and the term

    lambda x_bar, (p and U_S(x_bar)) or (b and F_0[x_bar]).    (3)

It has the specified actual extension and the same leaf profile as F_0. Hence

    D_tau(o) ≅ P(product_i D_sigma_i(o)) × S_tau.              (4)

The family S_tau is closed under all logical term operations evaluated in the full leaf algebra: lift finitely many allowed parameters to the root and transport their term. This includes quantifiers over the full leaf domains, not merely over the allowed profile family. Its individual parameters supply the marked a_v. At t, the image is exactly S_t={bottom,top}.

## 4. Finite definability: allowed profiles are fixed points of a subgroup

Let

    H := {g in G_0: g(alpha)=alpha for all relational tau
                                  and all alpha in S_tau}.  (5)

We prove

    S_tau = Fix_H(D_tau(v))                                  (6)

at every relational type. The inclusion from left to right is immediate. Since G_0 is finite, finitely many allowed parameters alpha_1,...,alpha_m already have common stabilizer H. For each element of G_0 outside H choose one allowed parameter that it moves.

Fix a reference enumeration c_1,...,c_n of the individuals, with c_1=a_v, and a reference enumeration d_1,...,d_k of the Boolean atoms. For each relational entity gamma there is a pure term

    T_gamma(u_1,...,u_n,w_1,...,w_k)

denoting gamma at these enumerations. At t use Boolean combinations of the named atoms. For each higher type, crisp identity and the already named finite input/output domains give an ordinary finite lambda case table. Individual outputs are never required.

Let beta be H-fixed, of relational type rho_1...rho_j t. Form the lambda term whose value at z_bar is

    exists u_1...u_n exists w_1...w_k [
      Enum_e(u_bar) and u_1=a
      and EnumAtoms(w_bar)
      and conjunction_i (alpha_i=T_alpha_i(u_bar,w_bar))
      and T_beta(u_bar,w_bar)[z_bar]].                        (7)

Enum_e is the finite exhaustive-distinct individual enumeration formula. EnumAtoms asserts that the w_i are distinct Boolean atoms and exhaust the atoms. In the rigid leaf algebra these enumeration conditions and parameter identities are crisp propositions, top when satisfied and bottom otherwise. Therefore the matching pairs of enumerations are exactly g(c_bar,d_bar), with g in H. At each such pair the output T_beta is g(beta)=beta, and at least the reference pair matches. The existential join in (7) is consequently beta as an entity. It follows from closure under terms with allowed parameters that beta belongs to S_tau. This proves (6).

Applying (6) at t shows that H is transitive on the k Boolean atoms. Indeed an H-fixed proposition is the union of H-orbits of atoms; there are only the two fixed propositions bottom and top exactly when there is one orbit.

This argument includes t among the relational output types. It does not assert that the root has every H-fixed leaf individual; the root individual domain remains singleton, and the extra individuals in (7) are bound inside the transported term.

## 5. Realizing every transitive subgroup and fixing the local algebra

Conversely, take any H<=G_0 transitive on the Boolean atoms. Use a rigid full k-world S5 component realizing B_(n,k), with the same n individuals and full finite function hierarchy at each component world. Transports within that component are identities. Add a singleton root and an arrow to each component world, transporting the unique root individual to the same marked leaf individual.

At the root use

    D_tau(o)=P(product_i D_sigma_i(o))×Fix_H(D_tau(v))         (8)

at every relational type, transporting each pair to its profile at every component world. Fixed profiles are closed under terms because H acts by term-algebra automorphisms, including full quantifiers. Every actual root extension is allowed. The ordinary coalescence closure proof therefore validates H and Logical Equivalence, hence C.

Transitivity gives precisely two fixed propositions at the leaf, so the root has four propositions. The root-only p and component-wide b satisfy the chain modal table. Every component world satisfies B_(n,k), and the root-like condition holds. Thus the model satisfies L_(n,k).

Conversely (4) and (6) give exactly (8) for every L_(n,k) world. This determines the full local logical structure. Application uses actual fibers and leaf application. Equality has actual truth iff the pairs are identical, and its leaf profile is the crisp equality of the two leaf profiles. Quantifiers have their actual truth over the current root domains and their leaf value given by the full leaf quantifier. Because all resulting source proposition profiles are H-fixed, these leaf values are bottom or top; together with the actual truth they determine the root proposition. Lambda abstraction is fixed by its actual extension and its transported leaf abstraction.

Conjugating H by G_0 relabels the leaf algebra while preserving its marked individual, and yields an isomorphic root typed logical structure. The next section proves that nonconjugate subgroups can be distinguished by finite pure sentences.

## 6. Pure finite orbit-relation isolators

For H<=G_0, take R of type e^n t^k t, meaning a relation with n individual arguments and k propositional arguments. For enumerations u_bar of the individuals and w_bar of the Boolean atoms, define the finite lambda term

    Orbit_H(u_bar,w_bar) := lambda x_1...x_n y_1...y_k,
      disjunction_((pi,rho) in H)
        [(conjunction_i x_i=u_(pi(i)))
          and (conjunction_j y_j=w_(rho(j)))].                (9)

All equalities are crisp at the leaf. This relation is the characteristic function, with values bottom/top, of the H-orbit of a complete ordered individual/atom frame.

Define psi_H(R,a) by

    exists u_1...u_n exists w_1...w_k [
      Enum_e(u_bar) and u_1=a and EnumAtoms(w_bar)
      and R=Orbit_H(u_bar,w_bar)].                            (10)

**The last clause is entity identity**, not a material biconditional on actual truth extensions. This distinction is essential for a non-Fregean leaf. Equivalently, one could use equality of the proposition-valued outputs on every input and leaf Functionality.

The stabilizer in G_0 of the reference orbit relation Orbit_H(c_bar,d_bar) is exactly H. The action of G_0 on complete ordered frames is free, so an element sends the H-orbit of the reference frame to itself exactly when it belongs to H. The relations satisfying (10) are precisely its G_0-conjugate orbit relations.

For a fixed source p in (1), put

    kappa_H(p) := exists a^e exists R^(e^n t^k t),
                              Box(not p -> psi_H(R,a)).      (11)

In the fixed-profile model for a transitive H'<=G_0,

    kappa_H(p) holds iff H' <= gHg^(-1) for some g in G_0.    (12)

Indeed a root R with the desired leaf profile exists exactly when some conjugate orbit relation is H'-fixed, equivalently when H' is contained in its stabilizer. The root actual extension is unrestricted. The boxed guard imposes the desired identity at every leaf-like target and no condition at root-like targets; the profile representation makes these conditions equivalent to the single chosen-leaf condition.

For a transitive subgroup H, define the closed pure cell

    J_(n,k,H) := E_1^e and E_4^t and exists p^t [
      Q_(n,k)(p) and kappa_H(p)
      and conjunction_(K proper subgroup of H) not kappa_K(p)]. (13)

The conjunction is finite. It may include all proper subgroups; proper subgroups not transitive on the Boolean atoms cannot contain a transitive H', so their kappa clauses are automatically false in this family and can be omitted.

Formula (12) proves that J_(n,k,H) holds exactly in the cases where H' is conjugate to H. If a conjugate of H' is contained properly in H, that actual proper subgroup K makes kappa_K true, violating (13). Conversely an H' conjugate to H cannot lie in a conjugate of a smaller subgroup. Thus each (13) is consistent and determines one local typed logical structure up to isomorphism. It is complete for closed pure sentences, and pointed-complete because the root individual domain is singleton. Semantic completeness for C gives the corresponding syntactic completeness claims.

One representative of each transitive conjugacy class gives a finite disjoint complete decomposition of L_(n,k).

## 7. Exact BF behavior and small cases

In every L_(n,k) world:

    BF_e holds iff n=1;
    BF_t holds iff k=1.                                      (14)

If n=1, all current and accessible individual domains are singleton, so all individual transports are onto and BF_e holds. If n>=2, use X=lambda x, x=a for the unique root individual a. Currently forall x Box(Xx) holds, but at every leaf there are individuals other than the image of a, so Box(forall x Xx) fails.

If k=1, all root-like t-maps are isomorphisms and all leaf t-maps are onto their two-element target, so BF_t holds. If k>=2, the leaf proposition domain has at least four entities while the image of the root t-domain is {bottom,top}. For a direct BF_t counterinstance, let X(z) say that z is one of the four current propositions bottom,p,not p,top. Every current proposition necessarily equals one listed member, by NI, so forall z Box(Xz) holds. At a leaf the transported list contains only bottom and top and omits the Boolean atoms; therefore Box(forall z Xz) fails.

Thus the complete cells include all four combinations of BF_e and BF_t. Useful smallest cases are:

| n,k | eligible subgroup classes | BF_e | BF_t |
|---|---|---|---|
| 1,1 | trivial only | true | true |
| 2,1 | trivial only | false | true |
| 1,2 | Sym(2) only | true | false |
| 2,2 | Sym(2) only | false | false |

For n=3,k=1 there are two classes, corresponding to trivial and swap subgroups on the two unmarked individuals. For n=1,k=3 there are two transitive classes on the Boolean atoms: the cyclic group of order three and Sym(3).

In the n=1,k=2 case, the leaf tt-domain has 4^4=256 functions. Its swap-fixed functions number 2*2*4=16: the values at bottom and top must be fixed propositions, and the value at one atom may be arbitrary, determining the other by equivariance. Hence the root tt-domain has 2^4*16=256 entities, but its transport image has only 16. Functionality_tt fails: choose identical actual extensions and leaf profiles given by the identity operation and Box. These profiles agree on bottom/top, the only transported source t-inputs, and differ on atoms. The resulting distinct root operations have equal entity-valued outputs on every current t-input.

## 8. Complete-chain cells versus their rigid leaves

Every chain world in (1) fails ND_t. Its actual p is distinct from bottom, but at a leaf p becomes bottom. Equivalently the source proposition p!=bottom is not necessary. Hence a B_(n,k) world, where ND_t is necessary, cannot satisfy any of these chain conditions.

Within a fixed chain cell, every other inequivalent chain cell is bottom as a proposition entity. At the actual world it is false because the cells determine distinct complete pure theories. At root-like targets its truth is unchanged because the t-map preserves every source proposition's truth. At leaf-like targets every chain cell is false by the preceding paragraph. Intensionality therefore identifies the other cell with bottom.

This last statement concerns the family of chain cells itself. It does not extend to their rigid leaf cells: a chain cell can and does make its own B_(n,k) leaf cell possible and false. The preceding BF chain note gives the simplest explicit example.

By the separately audited profile-root atomicity criterion, every J_(n,k,H) is consistently a propositional atom over pure Max, and pure Strong Possibility entails its atom assertion. The mutual entity-level exclusion just proved also supplies the protection condition for the previously audited arbitrary atomic/atomless pattern construction when applied to this countable family of chain cells alone.

## 9. Complete classification of every BF instance

The reconstruction also decides BF at every admitted type, not just e and t. First, at a finite source domain BF_sigma is equivalent to surjectivity of every outgoing sigma-transport. The forward direction uses the finite exhaustive list a_1,...,a_m and NI, exactly as in the earlier reconstruction: every current x necessarily equals one listed a_i, and BF_sigma moves the quantifier under the box. The reverse direction is the direct semantic Barcan argument using a preimage for every target entity.

At a root-like arrow, every type transport is bijective. Indeed source and target actual truth agree on the exact finite-cardinality sentence for that type, so their domains have the same finite size. Equality truth is also preserved, so the transport is injective. Thus only the leaf transport can obstruct BF. At a relational sigma its image is Fix_H(D_sigma(v)); consequently

    BF_sigma iff H acts trivially on D_sigma(v)              (15)

for relational sigma.

For the full leaf function hierarchy, let ker_sigma be the kernel of the G_0 action on D_sigma(v). Then

    ker_(sigma→tau) = ker_sigma intersection ker_tau.        (16)

One inclusion is immediate. Conversely, an element fixing every function must fix the constant functions, so it acts trivially on the output domain. If it moved an input, some function into two distinct output entities would distinguish that input from its image, contradicting pointwise fixation of the full function space. All output domains here have at least two entities, and all input domains are nonempty, so this argument applies at every admitted operation type.

The base e-kernel is the kernel of the individual-permutation factor; the base t-kernel is the kernel of the Boolean-atom-permutation factor. Induction using (16) yields the exact table:

| input type sigma | BF_sigma in J_(n,k,H) |
|---|---|
| e | iff n=1 |
| relational, containing no occurrence of e | iff k=1 |
| relational, containing an occurrence of e | iff H is the trivial subgroup |

For the second row, the kernel is precisely the t-kernel. Transitivity of H on the k Boolean atoms makes its action trivial exactly when k=1. For the third row, the type contains both e and t, and the common kernel of their two actions in G_0 is trivial.

In particular, when k>1, BF fails at **every relational type**. If also n>1, BF fails at every admitted type, including e. When k=1 but H is nontrivial, BF holds at all purely propositional types and fails at every relational type containing e. When H is trivial, all relational BF instances hold, even if BF_e fails because n>1.

The special e-row is essential: the root has only its marked individual, not every H-fixed leaf individual. Formula (15) was asserted only at relational types.

## 10. Functionality at each input/output pair

There is a general logical equivalence behind the corresponding Functionality classification. For every admitted input sigma and relational output tau, C proves

    BF_sigma iff Functionality_(sigma→tau).                  (17)

For BF_sigma implies Functionality, suppose forall x, f(x)=g(x). NI gives forall x Box(f(x)=g(x)); BF_sigma gives Box(forall x, f(x)=g(x)); C's modalized Functionality identifies f and g.

For the converse at output t, the BF antecedent forall x Box(Xx) is literally forall x Xx=top. Functionality identifies X with lambda x top. Applying the logical term Y↦forall x Yx to this identity yields

    (forall x Xx) = (forall x top) = top,

where the last identity is a pure theorem of C. This is Box(forall x Xx), as required. No optional assumption is necessitated.

To reduce a general relational output tau=rho_1...rho_j t to output t, use the constant-output embedding K(p)=lambda z_bar p. If X,Y of type sigma t have equal entity-valued outputs on every input, their K-lifted operations of type sigma→tau do too. Functionality at sigma→tau identifies the lifted operations. Choose any tuple z_bar of the nonempty output argument types and apply the identity-preserving term

    L(F) := lambda x, F(x)[z_bar].

Beta and eta recover X=Y, giving Functionality at sigma→t and hence BF_sigma. For the empty argument tuple tau=t, this is the preceding direct proof. This reduction uses only finitely many arbitrary arguments and no choice principle.

Thus the BF table in section 9 simultaneously classifies Functionality_(sigma→tau) for **every** relational output tau.

There are also explicit counterexamples in each failed case. Enumerate the finite current sigma-domain as a_1,...,a_m, and put

    g := lambda x^sigma, b and not disjunction_i(x=a_i).

For every current input a_j, g(a_j)=bottom as an entity, because the disjunction contains the self-identity top. If a leaf sigma-entity lies outside the transported list, all those leaf identities are bottom, while b is top; g has value top at that entity. Hence g is a nonbottom operation agreeing with the bottom operation on all current inputs. For any relational output tau, the lifted operation lambda x z_bar g(x) and the bottom operation give the same failure of Functionality at sigma→tau.
