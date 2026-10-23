# Explicit Barcan and Functionality failures under finite-signature Strong Possibility

22 October 2026. Original ordinary mathematical consequence of the independently audited finite-C5 signature cells. No database edits, human checking, Lean verification, or consistency claim for Strong Possibility.

## 1. Exact scope and result

Let Σ be any fixed **finite** signature of constants at the original admitted types. It may include individual names; its relational constants are c_1:τ_1,…,c_r:τ_r. Write SP_Σ for Strong Possibility with side condition Max(C(Σ))+P consistent. Empty Σ recovers the pure theory.

**Theorem.** SP_Σ refutes Barcan at every admitted input type α, including e and t, and refutes every Functionality instance with input α and relational output β. The proof supplies explicit predicates and counterfunctions. It is a consequence conditional on satisfaction of SP_Σ, not a proof that SP_Σ is consistent.

For an infinite relational signature with finitely many individual names, the separate e-Barcan failure and its input-e Functionality consequences still follow. The relational-type part below depends on a finite complete signature diagram and is not extended to infinite Σ.

## 2. A stable complete cell with four target propositions

Use B_(1,2) from `finite-c5-profile-cells-20261022.md`: one individual, four propositions, and C5. For a relational type τ let top_τ be its closed pure constant-top relation. Put

    Δ:=B_(1,2) ∧ AND_(i=1)^r(c_i=top_(τ_i)).

Every individual name has the same value at a Δ-point because its individual domain is singleton. Hence this is a complete pointed finite Σ-diagram when there are no individual names, and a complete closed finite Σ-diagram when there are. All named relational values are specified. The all-top interpretation is invariant under all Boolean-atom permutations, so no unresolved actual-atom orbit remains.

By the signature-cell theorem, the corresponding Σ-profile root verifies

    Con(Max(C(Σ))+Atom_t(Δ)).

Atom_t(Δ) is a universal Boolean combination of identities, so its SP_Σ instance and identity reflection give

    SP_Σ⊢Atom_t(Δ).                                      (1)

Δ itself is C(Σ)-consistent in the full finite Boolean-valued structure with two Boolean atoms. Signature Max, which SP_Σ entails, gives

    SP_Σ⊢Diamond Δ.                                      (2)

The formula Δ is stable:

    C(Σ)⊢Δ→Box Δ.                                       (3)

B_(1,2) is stable by the finite-cell proof. Each additional conjunct is an identity and is stable by NI; finite conjunction preserves stability. Thus at a point where Δ is true, its proposition entity is literally top. This detail is essential in the counterinstance below.

## 3. One fixed closed predicate witnesses failure of BF_t

Define the closed Σ-predicate

    Φ(p):=Δ→(p=top∨p=bottom).

SP_Σ proves

    ∀p Box Φ(p),             ¬Box∀p Φ(p).                (4)

For the first assertion, let p be any actual proposition. From (1), either Δ≤p or Δ≤¬p. These Boolean inequalities are identities and hence necessary. At every future point where Δ holds, (3) makes Δ=top; therefore the first alternative makes transported p=top and the second makes transported p=bottom. At every future point where Δ fails, Φ(p) is true by its material conditional. Consequently Box Φ(p). Since p was arbitrary among the actual propositions, ∀p Box Φ(p).

For the second assertion, use (2) to reach a Δ-point. Its proposition domain has four elements. Top and bottom are distinct and account for only two of them, so some local p is neither. At that point Φ(p) is false. Thus not Box∀p Φ(p).

The p used in the second paragraph is local to the target; it need not be transported from the source. Assuming that it has a source antecedent would erase precisely the Barcan failure. No future comprehension axiom or arbitrary-parameter signature extension is used.

## 4. Closed retracts give every relational input type

For any relational α=ρ_1…ρ_h t define closed pure terms

    c_α(p):=λx_1…x_h.p,
    r_α(X):=∀x_1…x_h X[x_1,…,x_h].

For the empty tuple these are identities. H's vacuous-quantifier laws and nonemptiness give the C-theorem

    r_α(c_α(p))=p.                                      (5)

The identity is theorem-level: the universally vacuous equivalence is logical, so Logical Equivalence/Intensionality applies. No actual evaluation tuple or individual name needs to be selected.

Put Φ_α(X):=Φ(r_α(X)). Applying (4) to r_α(X) gives

    ∀X^α Box Φ_α(X).

At a Δ-point choose a nonbivalent p and X=c_α(p). Equation (5) makes Φ_α(X) false. Therefore

    SP_Σ⊢(∀X^α Box Φ_α(X))∧¬Box∀X^α Φ_α(X).             (6)

This is a fixed closed Σ Barcan counterpredicate at every relational α, including t. It does not rely on a schema-level appeal to an unnamed witness.

## 5. The individual input case

Let Σ have exactly u individual constant symbols. The independently derived domain theorem in `audit-signature-to-pure-sp-20261022.md` §10 gives

    SP_Σ⊢E_m^e,       m=max(1,u).

Signature Max also gives Diamond E_(m+1)^e: a full extensional structure with m+1 individuals is a C(Σ) consistency witness, with arbitrary interpretations of the constants. Their genericity is not required in that target consistency model.

If u≥1, write the individual names as a_1,…,a_u and use the closed predicate

    Ψ(x):=(x=a_1∨…∨x=a_u).

SP_Σ entails that the names enumerate the actual domain. For each actual x, some equality x=a_i holds and is necessary by NI, so Box Ψ(x). At a possible E_(u+1) point the u transported names occupy at most u values; at least one local individual fails Ψ. Hence

    SP_Σ⊢(∀x Box Ψ(x))∧¬Box∀x Ψ(x).                    (7)

If u=0, pick any actual a:e, using only standing nonemptiness, and put Ψ_a(x):=(x=a). The actual singleton-domain theorem makes ∀x Box Ψ_a(x), again by NI. At a possible two-individual point at least one local individual differs from the transported a, so ¬Box∀x Ψ_a(x). The counterinstance is universally valid for each actual a; it does not add a nonlogical name to Σ. Existentially quantifying the predicate λx.x=a gives the closed negation of BF_e.

This argument uses only the finite-u individual-domain theorem and signature Max. It continues to hold when Σ has infinitely many relational constants but only finitely many individual names. No atom of a finite full signature diagram is required for this e-case.

## 6. Explicit counterfunctions for every allowed output

The following general implication is a C argument. Suppose a predicate P:αt satisfies

    ∀x^α Box Px,         ¬Box∀x^α Px.

Let β=η_1…η_h t be any relational output type and define

    f:=λx^α y_1^η1…y_h^ηh.top,
    g:=λx^α y_1^η1…y_h^ηh.Px.

For each actual x, Box Px says Px=top. Congruence under the constant-function construction then gives fx=gx as β-entities. Thus ∀x(fx=gx).

But f≠g. If f=g, NI and the logical application/evaluation laws would force every future x to satisfy Px: the common β-value is constant-top, and all the output argument types are nonempty. Formally C proves

    f=g → Box∀x Px

for these displayed lambda terms. This contradicts the second assumed assertion. Hence f,g witness the failure of Functionality at input α and output β.

Use P=Φ_α from (6) for relational α, and P=Ψ or Ψ_a from (7) for α=e. Every arrow type allowed by the map has relational output, so this covers every Functionality instance. No forbidden individual-output function is introduced. In the parameterized e-case, the same actual a is used throughout and can be existentially quantified in the closed counterexample.

## 7. Limits and comparison with the atom-splitting route

An alternative proof uses BF_t to make Atom(Δ) persistent for the distinctness-preserving modality and a duplicate-component coalescence to make ¬Atom(Δ) Max-consistent; SP then contradicts BF_t. The proof above uses the already established non-Fregean finite cell to exhibit the actual Barcan predicate directly, so no additional duplicate-component construction is needed.

The finite-signature requirement is substantive. If infinitely many relational constants remain unspecified, a finite diagram Δ generally leaves extra signature refinements and its claimed atomhood is not licensed by the finite complete-cell argument. The infinite-signature conclusion retained here is exactly the individual-input obstruction from §5 and the associated input-e counterfunctions.

None of these failures means that every individual instance of a Barcan schema fails. Equations (4), (6), and (7) give particular counterpredicates; ordinary tautological instances still hold. Likewise all Functionality **type instances** fail by explicitly constructed pairs f,g, not every pair of functions.
