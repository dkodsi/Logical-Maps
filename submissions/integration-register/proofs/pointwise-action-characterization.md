# Full action models: exact separation criterion

Ordinary proofs, 26 October 2026. The standing logic is C with its fixed relational type system. These are new arguments about the existing full action construction; no Lean verification or native record changes are claimed.

Let R be the evaluation object of a small category. In its full action model, propositions at V are all subsets of Out(V). Write q(u) for the membership bit of the arrow u in q. Transport is

```math
(a^t p)(u)=p(ua).
```

A raw profile f_d:P(Out(cod d))->2 for each d out of R specifies an admitted E:tt. At a:R->V its induced operation obeys

```math
(E_a q)(u)=f_{ua}(u^t q).
```

The full model's other types retain their standard full domains. Nothing below changes the construction or the interpretation of C.

## Main theorem

At R, the following are equivalent:

1. Every outgoing arrow has a retraction (a left inverse).
2. ND at type t.
3. Propositional separation by observers with pointwise conjunction preservation and pointwise involutivity.
4. The same separation with whole-operation involutivity retained.
5. The same separation with whole-operation conjunction preservation retained instead.

By contrast, retaining BOTH whole-operation identities is equivalent to every outgoing arrow being invertible, and to Rev at R.

The constructions proving the first five equivalences use only the retraction of the particular arrow being separated. They need no coherent family of retractions and no metatheoretic choice principle.

## 1. One split arrow gives a whole involution

Fix h:R->S, h different from 1_R, and choose j:S->R with jh=1_R. Define the raw profile

```math
f_d(q)=\begin{cases}
q(h),&d=1_R,\\
q(1_S)\mathbin\oplus q(j)\mathbin\oplus q(hj),&d=h,\\
q(1_{\mathrm{cod}(d)}),&\text{otherwise}.
\end{cases}
```

Here xor is addition of truth bits modulo two. These are arbitrary allowed raw extensions of a predicate on propositions, so fullness admits E.

At the root its operation is exactly the Boolean atom transposition exchanging 1_R and h and fixing every other arrow. Indeed its values at those two coordinates are p(h) and

```math
p(h)\oplus p(jh)\oplus p(hjh)=p(1_R).
```

All other coordinates remain p(d). Thus E preserves conjunction pointwise at R.

It is an involution as a WHOLE operation, including on every newly quantified successor proposition. For an arbitrary a:R->V, q subset Out(V), and u out of V, application gives

```math
(E_aq)(u)=\begin{cases}
q(hu),&ua=1_R,\\
q(u)\oplus q(ju)\oplus q(hju),&ua=h,\\
q(u),&\text{otherwise}.
\end{cases}
```

If ua=1_R, then (hu)a=h and the second application gives

```math
q(hu)\oplus q(jhu)\oplus q(hjhu)=q(u).
```

If ua=h, put v_0=ju and v_1=hju. Then v_0a=1_R and v_1a=h. The displayed formula swaps the v_0 and v_1 coordinates. It toggles the u coordinate by their xor; since that xor is unchanged by the swap, applying E_a twice restores u. More explicitly E_aq(v_0)=q(v_1), E_aq(v_1)=q(v_0), and the two xor contributions cancel. Coordinates in the third case are fixed outright.

Thus E_a^2 is the identity on ALL of P(Out(V)), for every a. The profiles of the whole terms lambda p.E(Ep) and lambda p.p are equal. This verifies whole involutivity, not merely its unboxed pointwise consequence.

## 2. One split arrow also gives a whole meet-preserving observer

With the same h and j, take instead

```math
f_d(q)=\begin{cases}
q(h),&d=1_R,\\
q(j),&d=h,\\
q(1_{\mathrm{cod}(d)}),&\text{otherwise}.
\end{cases}
```

At R this again swaps the two atoms 1_R,h, so it is pointwise involutive. At every successor, every output coordinate is a selected input coordinate. Hence conjunction is preserved on the entire proposition domain at every successor. This verifies the whole meet-operation identity. Whole involutivity is neither needed nor generally true for this second observer.

## 3. Separation and the exact frame criterion

If every outgoing arrow retracts, take different p,q at R and an arrow h in their symmetric difference. If h=1_R, the identity observer separates them. Otherwise either construction above has current truth value p(h) on p and q(h) on q. It separates them. This proves all three weakened separation principles, with no coherence requirement.

For completeness, ND_t is equivalent to every outgoing arrow retracting in a full action model. If all retract, each proposition transport has a left inverse and is injective. Conversely, if h has no retraction, the distinct root propositions {1_R} and zero become equal after h, violating ND_t.

Each weakened separation principle implies ND_t already over C. Here is the ordinary proof used for this direction. A current eligible observer is a Boolean automorphism, so it preserves top, bottom and the Boolean connectives. Apply it to C's unconditional equality-substitution identities and use its current inverse (itself) with the admitted predicate z |-> E(p=z). This gives E(p=q) iff p=q. Thus, when p and q are distinct, every eligible observer gives the same false truth value to the equality proposition (p=q) and bottom. Separation identifies those propositions, establishing necessary distinctness. This argument needs no whole operation identity beyond those already present in C.

When both observer clauses are whole, the established C equivalence with Rev applies. In full action models Rev implies necessary ND. If h:R->S has a retraction j, necessary ND gives a retraction k of j. Then k=k(jh)=(kj)h=h, so hj=1_S. Thus every h is invertible. Conversely if every root arrow is invertible then all arrows subsequently reachable from R are invertible: for b after a, b=(ba)a^{-1}. The reachable full model is a groupoid model and has C5, Atomicity and Rev. There is also a direct choice-free witness for the whole/whole separation: when h is invertible, hj=1_S, so the xor profile in section 1 simplifies at h to q(j). It is then exactly the coordinate-evaluation profile of section 2. The same observer therefore satisfies both whole identities. This proves the positive direction without a metatheoretic choice principle.

## 4. Current Plenitude and Functional Choice

In the usual full action construction in ZFC, the same five conditions are also equivalent to current Plenitude and current Functional Choice. These additional corollaries are logically separate from the choice-free observer constructions above.

One can verify current operation representation directly. Suppose all root arrows retract. Their actions are injective at every type. Fix an external set-function F:D_R(sigma)->D_R(tau), with relational output tau=rho_1 ... rho_n t. At each root arrow a:R->V prescribe the raw sigma tau profile as follows. If the input x at V is a^sigma(x_0) for a root x_0, use the current extension of a^tau(F(x_0)) on the arbitrary residual tuple at V. The preimage x_0 is unique. For inputs outside that image, prescribe the empty residual extension. Fullness admits this profile. Evaluating it on a root input x_0 recovers every raw coordinate of F(x_0), so its actual operation is F. No coherent choices of retractions are involved; injectivity alone makes the prescription unambiguous.

This represents every current functional relation and establishes Plenitude. With metatheoretic choice, an arbitrary current serial relation has a selecting set-function, which the same construction represents; hence current Functional Choice. Conversely Plenitude implies all-type ND over C, and Functional Choice implies Plenitude.

The recorded alternative derivation, checked with the proved-only Engine and no optional background, is

```math
\mathrm{RC}+\mathrm{ND}+\mathrm{Relational\ Choice}\ \Longrightarrow\ \mathrm{FC}.
```

The precise rule chain is:

- rigid-comprehension-r-implies-weak-rigid-comprehension-r;
- weak-rigid-comprehension-and-nd-imply-plenitude;
- relational-choice-and-plenitude-imply-functional-choice-r.

Full models have RC and, in the ordinary choice metatheory, Relational Choice. The ND supplied by retractions is all-type ND.

## 5. The double-retraction example

The existing full two-object double-retraction model has h:R->S and j_1,j_2:S->R with j_ih=1_R. It has ND, so it satisfies every weakened separation principle above. With coordinates q=(x,y_1,y_2,z_1,z_2) for (1_S,j_1,j_2,hj_1,hj_2), choosing j=j_1 in section 1 gives

```math
E_R(a,b)=(b,a),\qquad
E_S(q)=(x\oplus y_1\oplus z_1,z_1,z_2,y_1,y_2).
```

The latter squares to the identity. The model lacks coherent retractions, Strong Actuality and Gallin Extensional Comprehension. It nevertheless HAS current Plenitude and Functional Choice. The current proved-only Engine confirms these positive and negative verdicts. It fails BF_t and Rev. Consequently it must not be described as a countermodel to current Plenitude or current Functional Choice.

## Source and verification scope

- Full action semantics and C validity: topics/classicism/groups/full-action-models.yaml; Bacon and Dorr, Classicism, draft 16 May 2023, sections 3.4-3.5, pp.55-61.
- Retractions imply ND: topics/classicism/arguments/retractions.yaml; Classicism Proposition 3.24(i).
- Original double-retraction example: topics/classicism/models/full-two-object-double-retraction.yaml; Cian Dorr's suggestion of 6 October 2026, with full-action background as above.
- RC plus ND gives Plenitude: topics/classicism/results/weak-rigid-comprehension-and-nd-imply-plenitude.yaml; Classicism Proposition 2.16, p.33 and note 49.
- FC equivalence direction: topics/classicism/results/relational-choice-and-plenitude-imply-functional-choice-r.yaml and functional-choice-r-implies-plenitude-r.yaml.
- The single-arrow xor construction, its parallel whole-meet construction, and the resulting exact separation classification are new ordinary arguments in this note. They are not being attributed to the source authors.
