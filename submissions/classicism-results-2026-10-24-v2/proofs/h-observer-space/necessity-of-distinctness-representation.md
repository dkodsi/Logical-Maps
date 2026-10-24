# Necessity of distinctness gives exact semilattice and matching-quantifier representations

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.  No C, NI, Choice, domain finiteness or Functionality is assumed unless stated.

Over H, necessity of distinctness at type t removes the material-versus-pointwise gap for conjunction or disjunction separation. The same result covers conjunction with its matching universal bounds, and disjunction with its matching existential bounds. It works by constructing two-output principal tests; it does not impose endpoint bivalence on identity judgments.

## 1. Exact premise and statements

Use the defining formula of [ND at type t](../../source/topics/classicism/principles/distinctness-necessary-t.yaml):

$$
\mathrm{ND}_t:\quad
\forall x,y\,[x\ne y\to\Box(x\ne y)],
\qquad\Box r:=(r=\mathrm{Top}).
$$
Thus the premise used below is exactly

$$
\forall x,y\,[\neg(x=y)\to\neg(x=y)=\mathrm{Top}].
\tag{1}
$$
No C-dependent equivalent form of ND is substituted. In particular, (1) alone does not say that a false identity judgment is Bottom or that a true one is Top.

For a finite external type list Δ, let Meet_Δ mean:

- conjunction satisfies associativity, commutativity and idempotence;
- Top is its greatest element;
- at each σ∈Δ, primitive ∀σ supplies admitted greatest lower bounds in that meet order:
$$
  u\land\forall x^\sigma Fx=u
  \quad\leftrightarrow\quad
  \forall x^\sigma\,[u\land Fx=u].
  \tag{2}
$$
Define Join_Δ dually: disjunction is a join semilattice with least element Bottom, and every listed primitive ∃σ supplies the admitted least upper bounds.

Then over H+ND_t,

$$
\boxed{
\operatorname{Sep}_t[A\land M_{\rm mat}\land Q^{\rm mat}_\Delta]
\leftrightarrow\mathrm{Meet}_\Delta
\leftrightarrow
\operatorname{Sep}_t[A\land M_{\rm pt}\land Q^{\rm pt}_\Delta].}
\tag{3}
$$
Likewise,

$$
\boxed{
\operatorname{Sep}_t[Z\land V_{\rm mat}\land P^{\rm mat}_\Delta]
\leftrightarrow\mathrm{Join}_\Delta
\leftrightarrow
\operatorname{Sep}_t[Z\land V_{\rm pt}\land P^{\rm pt}_\Delta].}
\tag{4}
$$
The pointwise witnesses in both constructions have at most two outputs. The list Δ may be empty and need not contain t. Whole-operation identities require precisely the lifting described in §5.

## 2. Quantifiers on an admitted two-element chain

The following output-level fact is useful independently. Suppose conjunction is a meet semilattice, b is false, v is true, b≤v, and primitive ∀σ supplies the admitted GLBs in its order. Let G:σt be an admitted family with every value equal to b or v.

If every value is v, its GLB is v. If a value is b, its GLB is b: b is a lower bound of the whole family, and any lower bound is below that occurrence of b. Thus

$$
(\forall x^\sigma Gx)=
\begin{cases}
v&\text{if every }Gx\text{ is true},\\
b&\text{otherwise}.
\end{cases}
\tag{5}
$$
These are conditional identities, obtained from the GLB law and antisymmetry. In the all-v case the argument uses nonemptiness of the type σ. H supplies that for e and every relational type. No equality between two family objects, and no Functionality, is used.

Dually, if ∃σ supplies admitted LUBs in a join semilattice and G takes its values in a false/true chain b≤v, then ∃xGx is v if some value is v, and b otherwise. The endpoints of the chain need not be the fixed Top and Bottom, or global bounds of the semilattice.

Consequently, a material quantifier law for an observer valued in such a chain becomes a pointwise identity whenever the corresponding primitive quantifier supplies those bounds. The left side has a chain value; the right side has the same chain value by (5) and the material law.

## 3. The meet witnesses under ND

Assume the conjunction semilattice equations. For each parameter a define

$$
J_a(p):=(a\land p=a),\qquad
u_a:=(a=a),\qquad v_a:=\neg\neg u_a,\qquad f:=\neg\mathrm{Top}.
$$
The propositions u_a,v_a are true, and f is false, by H's truth rules. If J_a(p) is true, substitution using a∧p=a gives J_a(p)=u_a. If J_a(p) is false, (1) gives ¬J_a(p)=Top. Therefore

$$
\neg\neg J_a(p)=
\begin{cases}
v_a&\text{if }a\le p,\\
f&\text{if }a\not\le p.
\end{cases}
\tag{6}
$$
This calculation does not use the output equation ¬¬r=r. Define the admitted observer

$$
E_a(p):=\neg\neg J_a(p)\land v_a.
\tag{7}
$$
Its true value is v_a and its false value is b_a:=f∧v_a. They are distinct by truth, and b_a≤v_a. The semilattice principal-filter calculation gives

$$
E_a(p\land q)\leftrightarrow(E_ap\land E_aq).
$$
Both sides have the same value in the two-element meet chain, so this is the pointwise M identity. If Top is greatest, E_a accepts Top.

Now assume (2) at every listed type. The principal-filter truth profile and (2) give

$$
E_a(\forall x^\sigma Fx)
\leftrightarrow\forall x^\sigma E_a(Fx).
$$
The family λx.E_a(Fx) is admitted and takes values only in b_a,v_a. Section 2 converts this material law into the pointwise Qσ identity. The same E_a works for every type in the finite list.

The principal tests separate: if every E_a agrees on p,q, E_p gives p≤q and E_q gives q≤p, hence p=q. This proves the right-hand implication in (3). The material characterization and the implication from pointwise to material give the other directions, by [Truth profiles](truth-profiles-and-connective-reducts.md), §§6–7.

## 4. The join witnesses under ND

Assume the join-semilattice equations and define

$$
J_a(p):=\neg(p\lor a=a),\qquad f_a:=\neg(a=a).
$$
If p≤a, substitution gives J_a(p)=f_a, which is false. If p is not below a, ND gives J_a(p)=Top, which is true. Put

$$
D_a(p):=J_a(p)\lor f_a.
\tag{8}
$$
The two values are the false f_a and the true v_a:=Top∨f_a, with f_a≤v_a in the join order. The true value is not asserted to equal Top.

The principal-cut truth calculation says D_a(p∨q)↔(D_ap∨D_aq). The two-element join table makes this a pointwise V identity. If Bottom is least, every D_a rejects Bottom.

If each listed existential supplies admitted LUBs, its order law gives the material Pσ identity for this same principal cut. The dual of §2 turns it into a pointwise identity on the two output values. For distinct p,q, either p is not below q and D_q distinguishes them, or q is not below p and D_p does. This proves (4).

## 5. Endpoints, whole operations and full typed scope

The endpoint refinements are exactly the usual order bounds. On the meet branch, omit A if greatestness of Top is omitted. Add Z if Bottom is least, retaining only principal parameters a≠Bottom; these still separate. On the join branch, omit Z if leastness of Bottom is omitted. Add A if Top is greatest, retaining the cuts with a≠Top. Thus all four A/Z orientations have the matching material/pointwise equivalence over H+ND_t, with the corresponding fixed bounds in the intrinsic structure.

This is truth acceptance/rejection, not endpoint fixing: E_a(Top) may be v_a≠Top, and the dual observer's false value may differ from Bottom. Unlike the identity-bivalence representation, this proof does not justify replacing A or Z by endpoint-fixing clauses.

To obtain whole-operation identities at propositional scope, assume

$$
\operatorname{Fun}_{t,t},\qquad
\operatorname{Fun}_{t,tt},\qquad
\{\operatorname{Fun}_{\sigma t,t}:\sigma\in\Delta\}.
\tag{9}
$$
The first two lift the binary law, one input at a time; the last lift the quantifier laws as identities of the F-operations. With (9), replace every pointwise qualification in (3)–(4) by its whole-operation version. No unlisted Functionality is required for this propositional upgrade.

At full typed scope, append the full Functionality schema to the intrinsic order conditions. Then material, pointwise and whole-operation separation are equivalent over H+ND_t. This follows from [typed factorization](typed-separation-and-classicism.md), §2; full typed separation itself supplies all Functionality. The type list and the output type remain external schema indices.

Neither theorem recovers C. For example, the full-function four-proposition H model in [Local identity representation](representation-under-identity-bivalence.md), §6, has coordinatewise meet, negation and universal quantifiers, diagonal identity outputs, and a corrupted primitive disjunction. It satisfies ND_t because every false identity is (0,0), whose negation is Top=(1,1). It satisfies every displayed meet/GLB condition and all Functionality, but its disjunction-idempotence identity fails. This is the existing model with an additional directly checked ND verdict, not a new model record.

## 6. Finite-image normalization also preserves matching quantifiers

There is a second application of §2 which requires no ND premise. For every finite Δ and any A/Z orientation O, over H,

$$
\boxed{
\operatorname{Sep}_t[O\land\operatorname{FinIm}\land
 M_{\rm mat}\land Q^{\rm mat}_\Delta]
\leftrightarrow
\operatorname{Sep}_t[O\land\operatorname{Two}\land
 M_{\rm pt}\land Q^{\rm pt}_\Delta].}
\tag{10}
$$
The dual statement replaces M,Q by V,P. FinIm is internal Frege finiteness of the observer image; Two is the explicit at-most-two-output condition, as in [Finite-image normalization](finite-image-material-normalization.md).

For the forward direction, the left separation principle supplies the semilattice equations and the admitted GLB laws through its material characterization. Normalize each finite-image material observer by that note's two-fold construction. The replacement has the same truth profile, so all its material Q laws survive. Its two outputs form a meet chain, and §2 makes each Q law pointwise. Its M law was already pointwise. A/Z also survive. The replacement observers therefore establish the right separation principle.

If an original observer has a constant truth profile, that normalization uses a constant observer. The GLB of a constant admitted family is its constant value, so the matching pointwise Q laws still hold. The same observation handles constant observers on the join/existential side.

For the reverse direction, Two implies internal FinIm by the explicit one- or two-step Frege successor proof, and every pointwise law implies its material version. This proves (10). Full typed versions again include whole-operation preservation; at propositional scope use exactly (9).

Similarly, under internal Fin_t(All), the material/pointwise/whole-operation tier collapse from [Finite semilattice normalization](finite-semilattice-normalization.md) extends to these matching quantifier packages, with the same respective Functionality qualifications. Its truth-equivalent two-output replacements satisfy the hypotheses of §2.

### Joint lattice preservation and both kinds of indexed bound

The same finite-image result also covers the joint M,V signature, including both kinds of indexed bound. For finite lists Δ,Γ, put

$$
\Sigma:=\{M,V\}\cup Q_\Delta\cup P_\Gamma.
$$
Then, still over bare H,

$$
\operatorname{Sep}_t[O\land\operatorname{FinIm}\land\Sigma_{\rm mat}]
\ \leftrightarrow\
\operatorname{Sep}_t[O\land\operatorname{Two}\land\Sigma_{\rm pt}].
\tag{11}
$$
Indeed, the left principle gives the original distributive-lattice identities by the material M,V truth-profile argument. In particular the meet and join orders coincide. The meet normalization produces outputs b≤v, so they form a join chain as well as a meet chain. Both binary material laws consequently become pointwise identities on the same pair. Each listed Q law makes the primitive universal an admitted GLB in this shared order, and each P law makes the primitive existential an admitted LUB. Section 2 therefore upgrades all those laws simultaneously. The constant-profile cases use the GLB/LUB identity of a constant nonempty family. The reverse implication is again Two⇒FinIm and pointwise⇒material.

The same joint extension holds under Fin_t(All) without requiring FinIm in the material qualification: the global truth normalization supplies the two-output replacements directly. At full typed scope whole-operation preservation is equivalent, and the corresponding local Functionality instances suffice at propositional scope.

Equation (11) does not claim that an arbitrary distributive lattice already has an admitted separating material family. Nor does it use ND to turn arbitrary material M,V observers into finite-image ones. The ND principal tests of §§3–4 need not preserve the other binary operation.

Primitive negation remains outside these joint upgrades. A two-element lattice interval need not be closed under the original negation. Likewise, in the separate M/Q result the meet chain need not have the primitive join table, and a universal GLB law alone says nothing about primitive existential LUBs.

## 7. Remaining comparison

The general material-versus-pointwise M/V question over bare H is not settled here. The established sufficient regions now include internal finiteness of the proposition domain, finite-image material separating witnesses, local truth extrema, and ND_t. These are distinct stated routes; no implication between their extra premises is inferred.

For ND_t, the decisive information is the fixed value of a true inequality judgment, not persistence of an optional theorem or a global classical identity package. The normalization uses substitution and ordinary H truth rules throughout. The construction is uniform in the principal parameter a, so no choice of externally available homomorphisms is substituted for admission.
