# An exact Boolean-algebra test for the injective separation question

26 October 2026. Ordinary mathematical argument by OpenAI Codex. Direct source: `misc`, this note, unpaginated.


## 1. Why this test is relevant

There is an exact external Boolean-algebra criterion for a counterexample to

```math
C5+\mathrm{InjSep}+RC_{\rm all}\ \Longrightarrow\ \mathrm{SplitMono}
\tag{1}
```

within the full-hierarchy generic Boolean Henkin construction. That class already has boxed all-type Relational Choice and Zorn. Thus a positive value of the criterion below would refute even the proposed choice-strengthened implication, not merely the implication without choice. Conversely a single injective complete endomorphism with no complete left inverse does not suffice: the criterion incorporates full separation.

No claim is made that this construction represents every C5 Henkin model.

## 2. The ambient algebra and exact observer classes

Let B be a nontrivial complete Boolean algebra. Form the ambient full relational hierarchy A_e = N, A_t = B, A_(sigma tau) = all functions A_sigma to A_tau for relational tau. Choose H_theta large enough for all the fixed finite-type domains, function sets, and powersets used, and a countable elementary M containing the hierarchy and B. Use D_sigma = M intersect A_sigma and the M-generic ultrafilter worlds of the established construction. The Boolean truth and lambda-closure arguments do not require atomlessness; that condition was used in the earlier Cohen specialization to refute Actuality.

The construction and its truth lemma are described in [Generic Boolean choice with reversible observer separation, §1](generic-boolean-choice-boundary.md) and its cited source. [The choice-model proof, §§1–4](generic-boolean-choice-model.md) supplies genuine admitted rigid wellorders, boxed all-type RC, TC and Zorn. Those are construction inputs here.

Write H for the set of complete Boolean endomorphisms of B, A for its automorphisms, I for its injective complete endomorphisms, and L for the members of H having a left inverse in H. These are external sets in H_theta; choose theta large enough for their defining objects. The definitions have no reference to an ultrafilter.

**Observer identification.** An admitted operation E obtained by restricting an ambient M-function is Good at type t exactly when that ambient function belongs to H. Injectivity, reversibility and existence of a qualified left inverse likewise identify I, A and L on the M-functions.

For the forward direction, the whole preservation equations are literal equalities of restricted functions. Elementarity and faithful restriction turn their universal tests into the corresponding ambient equations: an ambient failure would have a witness in M. Good_t preserves the ambient joins of every B-indexed family. Every subset S of B is the range, with possible extra zero, of the B-indexed function taking x to x if x belongs to S and to 0 otherwise. Thus Good_t preserves every external join, as well as the Boolean operations. It is a complete Boolean homomorphism.

Conversely completeness preserves the Boolean join and meet giving every ambient quantifier at any admitted input type. The full composite identities therefore hold, and restriction preserves them. The equality clauses follow as in the existing generic model. The same E is qualified at every requested finite list. Current injectivity is a literal universal equality test and transfers by elementarity. For a complete Boolean automorphism its inverse is a complete Boolean map, definable from it and hence in M. More generally, if an ambient left inverse in H exists, elementarity returns one in M. This proves the identification, including the admission of inverse witnesses when they exist.

## 3. Boolean values of full separation

For a class T among H, A, I and L, define in B

```math
v_T=\bigwedge_{0<d\in B}\ \bigvee_{E\in T} E(d)
\tag{2}
```

These joins and meets are external Boolean operations in B. They are not an assumption of internal BC_t in the generic model. The relevant sets and functions are definable from B, so their resulting values belong to M.

At a generic world G,

```math
v_H\in G\iff OS,
\quad v_A\in G\iff Rev,
\quad v_I\in G\iff InjSep,
\quad v_L\in G\iff SplitMono
\tag{3}
```

To verify this, first use the exact propositional separation formula

```math
\forall d\,[d\ne0\to\exists E\,(T(E)\land Ed)]
\tag{4}
```

Each qualification predicate T(E) is endpoint-valued: it is assembled from literal function identities, and for L/A the inverse existential is over such tests. For a fixed d the Boolean value of the existential is exactly the inner join in (2), and the outer universal gives its meet. The generic truth lemma makes these Boolean quantifiers the classical quantifiers over the restricted M-domains. It is not an appeal to arbitrary-ultrafilter preservation of infinite joins.

The symmetric-difference argument identifies (4) with propositional separation. C5 Functionality and the same-observer qualification reduction identify that single instance with the full relational separation schema, exactly as in the existing decomposition notes. Thus (3) retains all output types, all finite qualification lists, and the whole-operation inverse requirements.

Put

```math
\delta_B=v_I\land\neg v_L
\tag{5}
```

**Countermodel criterion.** This generic construction has a world satisfying C5 + InjSep + RC_all + Zorn_all + not SplitMono if and only if delta_B is nonzero.

If delta_B is nonzero, it belongs to M and there is an M-generic ultrafilter containing it: start below it and meet the countably many required dense sets. Equation (3) gives the desired verdicts. Conversely any such world contains both v_I and the complement of v_L, so delta_B is nonzero. The choice and Zorn verdicts hold at every generic world independently of (5).

This criterion may be used with any fixed sufficiently large elementary hull containing B. It does not require a generic ultrafilter over the full external universe.

## 4. A more structural form using false principal intervals

Write o = v_H and r = v_A. Define

```math
j=\bigvee\{c\in B:\exists E\in I\ \forall p\in B\ (Ep\le c\Rightarrow p=0)\},
\tag{6}
```

and

```math
k=\bigvee\{\neg u:B\mathbin{\upharpoonright}u\cong B\}
\tag{7}
```

The isomorphisms in (7) are Boolean algebra isomorphisms; since the algebras are complete, an order isomorphism preserves all joins. The algebra B restricted to u has its relative Boolean operations.

The values j and k are exactly the Boolean values of the existing J_t and K_t formulas. For j this follows immediately from the crisp image-gap test and the final conjunct c. Here is the verification for k. A complete onto endomorphism F has greatest kernel element a = join{q:Fq=0}, with Fa=0. Its restriction to the interval below u = not a is a complete Boolean isomorphism onto B. A pair FE=I therefore contributes only kernel elements c below not u to K_t.

Conversely suppose alpha:B -> B restricted to u is an isomorphism, with inverse beta. Define

```math
F(q)=\beta(u\land q),\qquad
E(p)=\alpha(p)\lor(\neg u\land p)
\tag{8}
```

Both are complete Boolean endomorphisms of B, FE=I, and F(not u)=0. Their operation types are admitted, and elementarity supplies witnesses inside M whenever the ambient witnesses exist. Taking all eligible c and then their joins proves (7).

The established C5 decompositions therefore become exact Boolean equations

```math
v_I=r\lor(o\land j),\qquad
v_L=r\lor(o\land k),
\tag{9}
```

and hence

```math
\boxed{\delta_B=o\land j\land\neg r\land\neg k}
\tag{10}
```

For completeness, the transfer from the C5 theorems to identities in B is sound: their formulas have the stated Boolean values by the truth lemma, so a nonzero difference between either side would support an M-generic world contradicting the theorem. All computed values lie in M. This is also a direct way to verify that the full separation condition has not been omitted.

Thus the required algebra must have a nonzero region where complete endomorphisms collectively separate and an injective image-gap exists, while automorphisms do not separate and no isomorphic principal interval can discard that region. Ordinary unqualified Boolean retractions, such as ones supplied by extension theorems for Boolean homomorphisms, do not meet this test: the maps here must preserve all joins.

## 5. Status and sources

The reduction (2)–(10) supplies the exact generic-model counterexample criterion with all-type choice. The later [rigid Souslin construction](rigid-souslin-injective-separation.md), §§2–8, constructs an algebra with delta_B=1 under diamond; its §9 gives the resulting logical countermodel in ZFC through L. In contrast, the previous 2 x RO(Cantor squared) example with an inverse-free embedding does not supply the ordinary-separation conjunct. Homogeneous principal intervals retain the established local-homogeneity positive theorem.

The external construction obligation is therefore discharged. The resulting model refutes the full choice-strengthened implication; it does not add the chosen algebra's special structure as a premise of that implication.

Sources: the [injective decomposition](injective-separation-decomposition.md), §§1–6; the [left-inverse decomposition](left-inverse-separation-decomposition.md), §§1–6; [Boolean transversals](injective-observers-and-boolean-transversals.md), §§1–3; and [local homogeneity](local-homogeneity-and-split-observers.md), §§1–3. Each retains its original direct attribution and verification status. The generic construction and its boxed choice verdicts are the sources linked in §2. The current note is a reduction, not a consistency proof for the assigned separation counterexample.
