# Independent audit: finite C5 signature cells

22 October 2026. OpenAI Codex ordinary mathematical audit; not human checking or formal verification. Main records unchanged. Audited `finite-c5-signature-cells-20261022.md` §§1–8, its dependency `finite-c5-profile-cells-20261022.md` §§1–6, the relevant fixed-framework records, and the named-profile variant in `profile-root-construction-20261022.md` §12.

## Verdict

**PASS.** For every fixed positive finite m,k and every fixed finite relational-only signature Σ, the proposed pointed orbit formulas are consistent, complete for Σ-truth with one individual marker, form the required Boolean partition, and are simultaneously atoms in the audited singleton Σ-profile Max model. Their universal atomhood sentences transfer to SP_Σ. Consequently the exact number of atoms below B_(m,k) forced by SP_Σ is

    |(product_l H_(m,k),σ_l)/(S_(m−1)×S_(k−1))|.

Both stabilizers are necessary. The separate variant with u≥1 named individuals has orbit set

    [ {1,…,m}^u × product_l H_(m,k),σ_l ]/[S_m×S_(k−1)].

This remains a conditional description of any SP_Σ model, or an unconditional theorem of that axiom schema. Neither the finite profile witness nor the audit proves consistency of SP_Σ.

## 1. Full finite hierarchy: no hidden representability assumption

The single closed hypothesis K=□ND_t entails every instance of C5 by the proved type-t-to-all-types record. C5 supplies BF and Functionality at each admitted input/output type. The latter makes the evaluation map from a local operation entity to its actual argument-to-value function injective.

Induct on the syntax of types. D_e has m members and D_t has 2^k members. If D_α,D_τ are finite and τ is relational, every desired function f:D_α→D_τ is represented by the displayed finite equality-table lambda term. At an actual argument b, NI makes b=b literally top; ND makes b≠b′ literally bottom when b′ is different. Thus exactly one Boolean mask survives. The resulting relational value is f(b), as an entity, not merely a relation with the same actual truth extension. For a compound output τ, β and Functionality justify the pointwise identification with f(b). No output-e operation is used.

This proves surjectivity onto the entire finite function space, and Functionality proves injectivity. It is not necessary to assume a priori that the model is full or that every entity has a term name. Repeating the same induction with the displayed finite base enumerations x_i,a_j constructs names for every entity. The finite tables in §3 therefore genuinely exhaust all higher local domains.

One should retain the distinction between the two uses of Functionality: it first gives the cardinal upper bound, and it also turns pointwise equality for a relational output into equality of its value. Both are available under the same K hypothesis.

## 2. BF determines quantifier entities

Actual truth clauses alone would not determine an intensional quantifier's proposition value. The source correctly supplies the missing BF step. Given a local exhaustive enumeration b_1,…,b_d of type α, every current x satisfies a necessary identity x=b_i for some i. Hence

    ∀x □(x=b_1∨…∨x=b_d).

BF_α yields the necessary exhaustiveness of this tuple. For any current X:αt, every accessible point then satisfies

    (∀x Xx) ↔ (Xb_1∧…∧Xb_d).

The resulting boxed biconditional, followed by Intensionality, identifies the quantifier proposition with the finite meet. The existential case is its Boolean dual. This argument applies to every type after the finite-domain induction. No assumption that future objects are automatically images of current objects is made; BF is exactly what supplies the relevant exhaustiveness.

Consequently all logical operations in the local algebra, including modal terms defined through identity with top/bottom, are fixed by the finite full typed structure. There is no unclassified future-world parameter in its Σ-term truth.

## 3. Exact pointed isomorphism group and diagrams

Every automorphism restricts at e to a permutation of m individuals and at t to a Boolean automorphism, hence a permutation of the k Boolean atoms. Fullness and application determine its action at each higher type uniquely by recursive conjugation. Conversely every such pair extends to a typed logical automorphism because it preserves the finite Boolean operations and the finite quantifier meets/joins established above.

Actual truth selects one Boolean atom. The additional profile variable z selects one individual. On standard coordinates both must be fixed. Thus the group is precisely S_(m−1)×S_(k−1), not either singly stabilized group.

The enumeration formula requires z=x_1, a complete individual enumeration, a complete Boolean-atom enumeration and a_1 true. It therefore implements exactly this pointed group. Equality of a named constant with its finite-table term specifies its whole local entity. It does not merely specify its actual extension. Comparing two satisfying enumerations gives the claimed orbit equivalence, even for higher-type constants.

There are finitely many diagrams, each realized by the explicit full finite Boolean-valued model. At every B_(m,k)-point one is true, and distinct orbit diagrams cannot both be true. Outside B all are false. Therefore the partition and disjointness are genuine discharged C(Σ)-theorems. Necessitating their universal closures, using CBF to specialize the marker, and applying Intensionality gives the asserted entity identities. This is legitimate theorem necessitation, not necessitation of an optional B hypothesis.

## 4. Profile atoms and the universal transfer

For each diagram and each one-marker Σ-term T(z), pointed isomorphism gives a fixed actual truth value of T on all its diagram points. Applying this at every component object and descendant establishes the corresponding profile equality. Looking only at initially chosen pointed components would not suffice; the audited construction explicitly includes the required descendants.

The actual singleton root has infinitely many proposition entities, so B_(m,k) and every diagram have false actual coordinate there. Thus the profile dichotomy for p∧Δ becomes an equality of full root proposition entities with Δ or bottom. A finite diagram component proves Δ is nonbottom. This verifies atomhood. The same root works simultaneously for all diagrams and finite m,k; every individual quantifier at that root has its one actual witness.

In particular U=∀z Atom(Δ(z)) is Max(C(Σ))-consistent. Expanding Atom and Boolean order makes U a universal finite Boolean combination of identities. The terms inside those identities can contain the bound diagram quantifiers without changing that outer form. The universal-identity reflection lemma therefore gives D U→U. Its countertuple argument uses NI and finite disequality support; it does not require BF or C5 at the profile root. The SP side condition refers to the original fixed Σ throughout.

After transfer, choose any actual individual a using the background nonemptiness theorem. The finitely many Δ_ω(a) are distinct nonzero atoms, are pairwise disjoint and join to B. Finite distributivity shows every atom below B is one of these parts. There is no additional atom or missing orbit, and no individual constant has been added.

## 5. Counts, including higher constants and the named variant

The unary/proposition Burnside formula is correct. A fixed binary incidence matrix is constant on the cycles of the product row-column permutation; a proposition vector is constant on the Boolean-atom permutation cycles. Cycle-product orbit counts are gcds. Independent direct enumeration of binary-matrix orbits, fixing row1 and column1, gives the displayed table:

    m=1: 2, 4, 6
    m=2: 4, 16, 40
    m=3: 6, 40, 168.

The specializations k=1, m=1 and r=0 also check algebraically.

For arbitrary higher constants there is a useful fully explicit external counting recursion. For a base pair g=(π,τ), let F_σ(g^j) be the number of fixed points of its induced action on H_σ. At e this is the number of fixed individual points; at t it is 2 to the number of cycles of the atom permutation. At a function type αβ, the fixed functions satisfy f(g_α x)=g_β f(x). Thus

    F_(αβ)(g) = product_(C cycle of g_α) F_β(g^|C|).

One freely chooses the output on one representative of each input cycle, subject exactly to that output being fixed by the cycle-length power. Burnside then gives

    N_Σ(m,k)=average_(g∈S_(m−1)×S_(k−1)) product_l F_(σ_l)(g).

This independently confirms that higher-type constants are covered by the orbit theorem, without treating them as first-order incidence matrices.

With u≥1 named individuals, all root individual parameters can instead be replaced by closed names. The separately audited named-root construction consequently uses closed Σ-profiles and needs no anonymous marker. The ordered name tuple is allowed to repeat at target points; Max's actual inequalities between root names do not forbid later identifications. Its correct group fixes only the actual Boolean atom and acts on the name tuple. Its external Burnside count is

    average_(g=(π,τ)∈S_m×S_(k−1))
       (number of fixed points of π)^u · product_l F_(σ_l)(g).

For u=1 the usual pointed-set/stabilizer correspondence recovers the relational-only count. Setting u=0 in this named formula does not remove the need for a marker in the relational-only profile argument; that would usually change the answer.

## 6. Assumptions and status

The audit uses the fixed C/H semantics and its completeness, the proved C5 consequences, and the previously audited singleton/named profile closure constructions. All signatures and displayed diagrams are finite; m,k are fixed positive external integers. There is no infinitary diagram, internal uniform sequence of atom counts, Choice principle, added named individual, or signature-conservativity assumption. The empty-signature specialization is the pure case, rather than a change to the bundle's convention for nonempty signatures.

No mathematical repair is needed. The additional counting recursion above is an optional consequence, not a condition of the source theorem. No main records or formal-verification statuses were changed.
