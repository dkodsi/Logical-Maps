# Relational Choice forces Transversal Choice in symmetric ideally-full map categories

OpenAI Codex research argument, 22 October 2026. The coordinating agent independently checked the multiobject extension. This strengthens the one-object result in `rc-alone-higher-type-audit.md`. It is a semantic theorem for the explicitly specified full profile construction; it is NOT a proof of RC⇒TC in arbitrary C-models.

## Theorem and scope

At an evaluation object V in a symmetric ideally-full intensional action hierarchy satisfying the profile rules below, for every admitted type τ,

    Relational Choice_(τt,τ) at 1_V  ⇒  Transversal Choice_τ at 1_V.

**Exact local characterization (ZF metatheory).** Suppose the type domains are sets and permitted supports are closed under finite unions. Then the following are equivalent for an output type τ at V:

1. The membership-selector instance of RC_(τt,τ) holds.
2. There is a permitted N⊆I_V whose pointwise stabilizer acts trivially on D_τ(V), and the external set D_τ(V) is well-orderable.
3. RC_(α,τ) holds for EVERY admitted input type α.
4. There is an admitted actual well-order of D_τ(V), where least-element quantification initially ranges only over admitted properties.

In particular the full RC and TC schemas are equivalent throughout this model class. The local statement TC_τ⇒(2) is NOT asserted. The proof of the characterization and the distinction between external and internal choice appear in §§6–7.

The proof needs only the membership-selector instance of the indicated Relational Choice instance. It is choice-free in the metatheory. It permits multiple objects, arrows that are noninvertible or collapse pinning points, return arrows between objects, arbitrary induced symmetry actions at higher types, and the variants in which the individuals are a singleton while a different base supplies pinning sets.

Consequently no model in this class can satisfy the full Relational Choice schema while refuting Transversal Choice. The class is the full symmetric profile construction described below, not arbitrary category semantics, arbitrary full action models with different constraints, or a restricted Henkin subhierarchy which may omit symmetric pinned profiles.

The local sources for the construction rules are `topics/classicism/writeups/symmetric-old-new-individuals.md`, the section “The model” (especially its explicit symmetric/pinned clauses), and `topics/classicism/groups/symmetric-ideally-full.yaml`, `symmetric-domains`. Those reproduce the rules attributed there to Dorr's Definitions 15–18. The theorem here is a new research argument, not a claim quoted from that draft.

## 1. Exact construction assumptions

Let C be a category of maps on pinning carriers I_W, with arrows w:V→W acting on those carriers. For the ZF characterization, the relevant profile families and transports are set-indexed, as in the recorded finite-object constructions; for example, it suffices that this map category is small. No assertion about an uncoded proper-class category is intended. Each object W has a designated group G_W of automorphisms of its carrier which are arrows W→W. For each admitted type τ there is a set D_τ(W), and each arrow has its usual coherent transport action on entities. In particular G_W acts as a genuine group of bijections on D_τ(W). Application and satisfaction are equivariant under these symmetry arrows.

For the property type τt, an intension A at V is described by profiles

    A_w ⊆ D_τ(W)       (w:V→W).

For a more general relational type, use profiles of tuples of entities at W. Transport is precomposition:

    (h_*A)_k = A_(k∘h).

The hierarchy admits EXACTLY ALL profiles satisfying the following conditions (the proof uses only the “all” direction, and that every chosen selector has a pinning set):

* Symmetry: A_(g∘w)=g_*[A_w] for every w:V→W and g∈G_W.
* Pinning: some permitted support N⊆I_V pins A, meaning A_w=A_w′ whenever w,w′:V→W have the same target and agree on N.

In the recorded construction the permitted supports are finite. The argument below itself does not use finiteness: it works for any support ideals with these same profile, transport, symmetry, and full-admission laws. This observation does not construct new C-models for arbitrary support ideals; their model conditions must still be checked separately.

The pinning carrier I_V need not equal D_e(V). The proof never uses faithfulness of the symmetry action on the individuals or on D_τ(V).

For a set T⊆I_W write

    (G_W)_T := {g∈G_W : g fixes every member of T},
    Fix_τ((G_W)_T) := {y∈D_τ(W) : ∀g∈(G_W)_T, g_*y=y}.

## 2. A membership selector forces a trivial stabilizer action

As in the usual typed C semantics, first assume D_τ(V) is nonempty. The harmless empty-domain case is addressed in §7. Let S be an actual total functional selector for

    U(A,y) := Ay ∨ ¬∃z Az,

at input type τt and output type τ. Let N⊆I_V pin S. Define the following COMPLETE property intension A at V, for every arrow w:V→W:

    A_w := D_τ(W) \ Fix_τ((G_W)_(w[N])).

It is N-pinned: if w,w′ agree on N, then w[N]=w′[N], so the displayed profiles are equal. No injectivity of w is used.

It is symmetric. For g∈G_W,

    (G_W)_(g[w[N]]) = g (G_W)_(w[N]) g^(-1),

and the induced G_W-action is a group action on D_τ(W). Hence

    Fix_τ((G_W)_(g[w[N]]))
       = g_*[Fix_τ((G_W)_(w[N]))],

so A_(g∘w)=g_*[A_w]. Ideal fullness therefore admits A.

For every g∈(G_V)_N, pinning implies g_*S=S and g_*A=A AS ENTITIES. To check the full-intension equality, take any later k:V→W: the arrows k∘g and k agree on N, so all their profiles agree. This is stronger than mere invariance of the root extensions.

If A_(1_V) were nonempty, S would select y∈A_(1_V). Equivariance and the two entity equalities yield S(A,g_*y) for every g∈(G_V)_N. Actual functionality then gives g_*y=y for every such g, contradicting y∈A_(1_V). Therefore

    Fix_τ((G_V)_N)=D_τ(V).                            (1)

Thus one pinning set of S has a pointwise stabilizer acting trivially on the entire ACTUAL τ-domain. The stabilizer need not be the trivial group; no faithful-action assumption is needed.

## 3. Root-local canonical codes for all actual subsets

For EVERY external subset E⊆D_τ(V), define an intension B^E at V by

    B^E_w = g_*[E]
      if target(w)=V and w|N=g|N for some g∈G_V;
    B^E_w = ∅ otherwise.

This definition uses profiles ending back at the root V and assigns the empty extension to profiles ending at other objects. Return arrows are allowed.

The displayed value is well-defined. If g_1,g_2∈G_V agree on N, then g_2^(-1)g_1∈(G_V)_N. By (1) this symmetry acts trivially on D_τ(V), so g_1*[E]=g_2*[E]. The profile may equivalently be defined as the union of these equal images, avoiding any external choice of a matching g.

Pinning is immediate for parallel w,w′ agreeing on N: they have the same target and exactly the same matching condition and value. This remains true after every further transport, including return arrows, because k∘w and k∘w′ still have the same target and agree on N.

For symmetry, if the target W is not V, both profiles are empty and G_W preserves that case. If W=V and w matches g∈G_V, then h∘w matches h∘g for h∈G_V and

    B^E_(h∘w)=(h∘g)_*[E]=h_*[B^E_w].

If w has no matching symmetry, neither does h∘w, since h is invertible. Thus B^E is symmetric and N-pinned, so ideal fullness admits it at type τt.

At the identity, g=1_V qualifies and (1) makes all qualifying values equal to E. Therefore

    B^E_(1_V)=E.                                    (2)

The entire profile B^E is a specified function of E and N. Equal external subsets yield literally the same intension, not merely two actually coextensive codes. This is an EXTERNAL canonical coding construction in the semantic proof. It does not assert an admitted operation A↦B^(A_(1_V)); such an operation would require a separate transport/admissibility argument and can fail.

## 4. Construct the transversal without additional choice

Let R be any admitted actual equivalence relation on D_τ(V). For each a∈D_τ(V), let

    E_a := {b∈D_τ(V) : R(a,b) actually}.

This is nonempty. Apply the EXISTING selector S to the canonically specified code B^(E_a). By (2) its unique selected value y_a belongs to E_a. If R(a,b), then E_a=E_b, hence the input entities B^(E_a), B^(E_b) are identical and functionality gives y_a=y_b.

The set

    T := {y∈D_τ(V) : ∃a, S(B^(E_a),y) actually}

exists by Separation (or equivalently Replacement of the uniquely defined values). It contains exactly one element of each actual R-cell. Section 3 admits B^T, whose actual extension is T, proving Transversal Choice at τ.

No new metatheoretic choice principle has entered: S and its support N are single witnesses supplied by the hypothesis and the construction rules; the codes B^E are explicitly defined; each y_a is unique; and T is obtained by Separation/Replacement.

## 5. Boundaries and consequences

* Multiobject behavior is harmless here because symmetry acts within a target and pinning compares parallel arrows. The root-target split in §3 is preserved by both requirements.
* Noninvertible arrows and collisions in w[N] are harmless in §2. Only the g's belonging to designated symmetry groups are inverted.
* The proof applies separately at each admitted τ and does not produce one common support N for all types.
* With D_e(V)=I_V and a faithful base action, (1) says the pointwise stabilizer of N is the identity group, recovering the original finite-base corollary when supports are finite.
* For an arbitrary admitted τ, (1) says only that this stabilizer acts trivially on D_τ(V), which is exactly what §3 requires.
* A sparse Henkin completion can omit the moved-element intension A of §2 or root-local codes B^E of §3. This theorem does not exclude such a completion. Checking that its domains remain closed under all formulas and all RC witnesses remains the separate unresolved construction problem.
* The theorem gives actual extension fullness at τ as an intermediate semantic consequence of the membership selector. It does not give Boolean Completeness, Actuality, Plenitude, or a canonicalization operation.

## 6. Exact output-type characterization

Work in ZF, with set-sized type domains, and assume the allowed support ideal at V is closed under finite unions. These are metatheoretic hypotheses on the construction, not extra object-language choice or modal principles.

### 6.1 Necessary external choice

A membership selector S gives a support N with trivial stabilizer action by §2. Sections 3–4 provide a canonically specified admitted code B^E for EVERY external E⊆D_τ(V). Therefore

    c(E) := the unique y with S(B^E,y) actually

is an external choice function on ALL nonempty subsets of D_τ(V). This function exists by Separation/Replacement; its definition makes no new choices.

In ZF, such a choice function implies that D_τ(V) is well-orderable: recursively choose c of the remaining elements along the Hartogs ordinal of D_τ(V); the recursion must exhaust the set before that ordinal, since otherwise it would inject the Hartogs ordinal into D_τ(V). Conversely, a well-order supplies the least-element choice function. This standard argument uses the full powersets and transfinite recursion of the METATHEORY, not a power-object or recursion principle inside C.

Thus the membership instance implies condition (2) in the characterization.

### 6.2 A profile lemma for invariant root relations

A useful generalization of §3 is immediate. Let E be an arbitrary external relation on a finite tuple of actual type domains at V, and suppose the pointwise stabilizer (G_V)_N fixes E SETWISE (it need not fix its argument entities pointwise). Define

    B^E_w = g_*[E]
       if target(w)=V and w|N=g|N for some g∈G_V,
    B^E_w = ∅ otherwise.

Two matching g's differ by an element of (G_V)_N, which fixes E setwise. Therefore the value is well-defined. The pinning and symmetry proofs of §3 apply verbatim, and the root profile is E. Ideal fullness admits this relation at its appropriate relational type.

This is the only representation lemma needed for the converse.

### 6.3 Sufficiency for every input type

Suppose N_τ is an allowed support with (G_V)_(N_τ) acting trivially on D_τ(V), and fix an external well-order of D_τ(V). Let α be ANY admitted input type and let U be an admitted actual serial relation from α to τ. Choose a support M for U and put

    N := N_τ ∪ M,
    H := (G_V)_N.

This is an allowed support by finite-union closure. H fixes U as an entity and every actual τ-output pointwise. Consequently, for h∈H and x∈D_α(V), the actual U-fibers satisfy

    U_(h_*x) = U_x.

Indeed equivariance gives U(h_*x,h_*y) iff U(x,y), and h_*y=y for every output y.

Define an external root graph E by letting E(x,y) hold exactly when y is the well-order-least member of U_x. Seriality makes this a total functional graph contained in the actual extension of U. Equality of the displayed fibers implies E(h_*x,h_*y) iff E(x,y), so E is H-invariant, although H may move the input x.

Apply §6.2 to E and N. The resulting admitted graph has actual extension E, so witnesses RC_(α,τ). Its other-world profiles need not be functional or contained in U there; the target instance is unboxed and actual. Thus condition (2) implies (3), and (3) plainly implies the membership instance (1) by taking α=τt.

Equivalently, condition (2) may be stated with an external choice function on all nonempty subsets of D_τ(V) in place of a well-order. Using that version makes the sufficiency proof choose c(U_x) directly and requires no invocation of Zermelo's theorem. No choice on input orbits is needed because the output fibers themselves are equal along H-orbits.

### 6.4 Full-schema conclusion and limitations

The local implication from membership RC to TC_τ was proved in §4. Hence full RC implies full TC in this semantic class. Conversely full TC implies full RC by the established theorem of C. Combining these facts yields the exact full-schema characterization:

    full RC ⇔ full TC
       ⇔ for every admitted output type τ,
          some allowed support has trivial stabilizer action on D_τ(V)
          and D_τ(V) is externally well-orderable.

The supports and well-orders may depend on τ. This is a family of existence assertions; it does not require one common support or a simultaneously chosen family of well-orders. If the semantic metatheory is ZFC, external well-orderability of each set domain is automatic, so the criterion reduces to existence of a permitted support whose stabilizer acts trivially on that type. This is a metatheoretic specialization, not an added choice principle inside C.

One isolated TC_τ instance is weaker in scope than full TC, and no converse from isolated TC_τ to the stabilizer/well-order criterion is claimed. Likewise the external well-order from §6.1 need not by itself be represented as an admitted internal relation without the support/full-profile argument; the two ingredients of condition (2) are both essential to the proved converse.

## 7. Equivalent existence of an admitted actual well-order

Condition (2) also implies that an external well-order of D_τ(V) is representable as an admitted binary relation. Its entire graph is invariant under (G_V)_(N_τ), since this group fixes every argument pointwise. The root-profile representation lemma §6.2 therefore supplies an admitted relation with exactly that actual graph. It satisfies the internal well-order condition because every admitted nonempty property has an extension that is an external nonempty subset of the well-ordered set. This proves (2)⇒(4).

Conversely, suppose an admitted relation L is actually transitive, antisymmetric and total, and every nonempty admitted property of τ has an L-least instance. This is the exact unboxed well-order definition in `topics/classicism/principles/well-ordering-r.yaml`. Let N pin L. Form the moved-element property A of §2 using this same N:

    A_w = D_τ(W) \ Fix_τ((G_W)_(w[N])).

It is symmetric and N-pinned, and hence admitted. Every g∈(G_V)_N fixes both A and L as ENTITIES. If A had a nonempty actual extension, its unique L-least instance y would be carried by every such g to another L-least instance. Antisymmetry gives g_*y=y for every g∈(G_V)_N, contradicting y∈A. Thus (G_V)_N acts trivially on D_τ(V).

Section 3 now admits a canonical code B^E for EVERY external E⊆D_τ(V). Applying the assumed INTERNAL least-element condition to each nonempty B^E shows that the actual relation L has a least element in every nonempty EXTERNAL subset. The pointwise order axioms already range over the full actual domain. Therefore the actual graph of L is an external well-order, proving (4)⇒(2).

The intermediate use of A is essential: one cannot silently replace admitted-property well-foundedness by external well-foundedness before establishing root extension fullness. The proof derives that fullness first.

For completeness, if an extended convention permits D_τ(V)=∅, the criterion is still valid: every stabilizer acts trivially on the empty set and its unique order is a well-order. The all-empty profile admits the empty order and every empty root graph. Any actual serial relation into the empty output domain can only have an empty input domain, so the empty graph witnesses the corresponding RC instance. The membership-selector implication is then vacuous, and §2's nonempty-output construction is unnecessary. This uses at least the empty allowed support, as any support ideal supplies. The recorded C hierarchy ordinarily has inhabited type domains.

Consequently, in this semantic class, the single membership-selector instance is already equivalent to actual Well-Ordering at the output type. The full-schema characterization can be written

    full RC ⇔ full TC ⇔ full Well-Ordering.

This last equivalence is local to the stated symmetric ideally-full construction. The implication from internal Well-Ordering at τ to RC_(α,τ) also has the familiar direct C proof: choose the L-least member of each admitted fiber λy.Uxy. Nothing here proves the difficult converse in arbitrary C-models.

## 8. Sharpness: isolated TC at the individual type is weaker

There is a simple model in the specified class where TC_e holds but membership RC_(et,e) fails. This is an additional semantic example, not a claim about a newly entered map record.

Take one object with pinning carrier and individual domain I=N, all permutations of I as arrows, the same full symmetric group as designated symmetries, and the finite-support ideal. This is DISTINCT from the recorded non-symmetric `finite-support-permutations` model, which admits all finitely pinned profiles without the additional full-group symmetry requirement and satisfies RC. Use the symmetric ideally-full hierarchy described in §1. The cited construction theorem is the same one recorded for these hierarchy rules; no further completion is proposed here.

An admitted relation R on individuals with finite support N has an actual extension invariant under every permutation fixing N pointwise. Conversely, any actual finite-support relation E on individual tuples is admitted: put E_w=w[E]; symmetry is immediate, and equality of w,w′ on a support gives equality of their images. In particular every finite or cofinite subset of I is admitted.

Suppose R is an admitted actual equivalence relation and N is one of its finite supports. Write O=I minus N. The full symmetric group on the infinite set O acts transitively on ordered pairs of distinct elements. Consequently the restriction of R to O is either equality or the universal relation.

* If it is equality, no element n∈N can be R-related to any element of O. Otherwise invariance would make n related to every element of O, contradicting the equality case by transitivity. The R-cells therefore consist of all the singleton cells in O and a finite partition of N. Choose one representative of each cell in that finite partition and adjoin all of O. The resulting transversal is cofinite, hence admitted.
* If the restriction is universal, O lies in one R-cell, which may also contain some elements of N. All remaining cells form a finite partition of the rest of N. Choose one member of O and one representative of each remaining cell. The resulting transversal is finite, hence admitted.

Only finite choice is used, which is a theorem of ZF. Thus this model satisfies the isolated TC_e instance.

On the other hand, a hypothetical membership selector S of type (et)et has some finite support N. The admitted cofinite property with extension I minus N is fixed as an entity by every element of G_N. S is fixed by the same stabilizer. Its uniquely selected member would therefore be fixed by every element of G_N, but no member of I minus N has that property. This contradiction refutes RC_(et,e).

Thus even inside this symmetric ideally-full class, TC_e does not imply the support/well-order criterion for the output e. The local characterization must keep membership RC or actual Well-Ordering as its local premise; the equivalence involving TC is correctly stated only for the full schema.
