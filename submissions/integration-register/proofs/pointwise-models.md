# Model lane: pointwise reversible separation

Ordinary mathematical arguments, 26 October 2026. No Lean verification or native-record changes. All statements use the fixed relational type system and C.

Write K_pt(E) for current pointwise conjunction preservation and involutivity:

```math
\forall p q\,E(p\land q)=Ep\land Eq,\qquad \forall p\,E(Ep)=p.
```

Write S_pt for propositional separation by these observers, and P_sep for

```math
\forall p q\,\Box\Bigl[(\forall E\, .\,K_{pt}(E)\to(Ep\leftrightarrow Eq))\to p=q\Bigr].
```

## 1. The finite full retract does not satisfy P_sep

Its root proposition domain is 2^2 and its target proposition domain is 2^3. The transports are

```math
H(a,b)=(b,a,b),\quad J(x,y,z)=(y,z),\quad K(x,y,z)=(z,y,z).
```

Any admitted operation at the target has its last two output coordinates determined by (y,z), because these coordinates lie after the arrows j and k. If its current operation is a Boolean automorphism, it permutes the three atoms. Thus the last two output coordinates must permute y,z, and the first output coordinate must be x. Every current eligible observer at the target therefore preserves current truth. The old root proposition (1,0) transports to (0,1,0), distinct from zero but not separable from zero by a current eligible observer. P_sep fails.

This does not conflict with root S_pt: the parity observer has root operation (a,b) -> (b,a), target operation (x,y,z) -> (x xor y xor z,z,y), and is eligible at the root.

## 2. P_sep forces reversibility in every full action model

The argument in this section concerns the full action model class. The independent
identity-reflection argument in [REPORT.md](pointwise-reversible-separation.md), section 4, now proves the
same implication over arbitrary C. The semantic argument below is retained as
an additional explanation of the result in full models.

At an object V, propositions are all subsets of Out(V). A current eligible observer acts as the inverse-image operation of an involutive permutation pi of Out(V). For each outgoing arrow g, let I_g be the set of arrows factoring through g. Naturality of an admitted operation preserves the kernel of transport along g. Consequently pi(I_g) is contained in I_g: otherwise two propositions agreeing on I_g, but differing at pi(u) for some u in I_g, would acquire different transported observer values. Since pi is involutive, pi(I_g)=I_g.

If pi(1_V)=g, then pi(g)=1_V. Since g belongs to I_g, preservation of I_g shows that 1_V factors through g. Therefore g has a retraction.

Assume P_sep at R. In particular S_pt holds there. Applying S_pt to each singleton {h} and zero shows that every h:R->V has a retraction. Now apply P_sep to the OLD propositions {1_R} and zero at h. Their transported difference is the nonempty set of retractions j:V->R with jh=1_R. A separating observer at V must have pi(1_V)=j for one such retraction. By the preceding paragraph j itself has a retraction k, so kj=1_V. Then

```math
k=k(jh)=(kj)h=h,
```

and hence hj=1_V. Every outgoing arrow from R is invertible. Every arrow reachable from R is invertible as well: if a follows h, both h and ah are invertible, so a=(ah)h^{-1}. Thus the reachable action category is a groupoid and all type transports are bijections. The model has C5, BF, Atomicity and Rev at R.

This semantic argument alone does not cover arbitrary atomic or Henkin C models.
The global proof in [REPORT.md](pointwise-reversible-separation.md), section 4, removes that restriction.

## 3. Current Functional Choice and infinity do not repair S_pt

There is a full C model with

```math
\mathrm{FC}+S_{pt}+\Box\mathrm{InfAx}_e+\Box\mathrm{InfAx}_t+\neg\mathrm{BF}_t.
```

Thus it also satisfies the corresponding infinity schemata and fails Rev. This uses current FC, not boxed FC.

Take the product of the two-object retract category with the one-object group Z, and evaluate at the retract's root R. Give every object the fixed individual domain N, with trivial individual transport. The root and target arrow sets are respectively 2 x Z and 3 x Z. Use the full relational domains throughout.

Every arrow a out of R has a unique retraction r_a. Explicitly, (1_R,n) has retraction (1_R,-n), and (h,n) has retraction (j,-n). If b follows a, uniqueness gives

```math
r_{ba}b=r_a.
```

Fix any admitted input type sigma, relational output type tau, and any external set-function F:D_R(sigma)->D_R(tau). For each arrow a out of R define

```math
F_a=a^\tau\,F\,r_a^\sigma.
```

These functions are natural, because

```math
b^\tau F_a=(ba)^\tau F r_a^\sigma
=(ba)^\tau F r_{ba}^\sigma b^\sigma
=F_{ba}b^\sigma.
```

To check admission explicitly, write tau=rho_1 ... rho_n t. At an arrow a:R->V, assign the raw extension consisting of tuples (x,z_1,...,z_n) such that F_a(x)[z_1,...,z_n] is true at V. Fullness admits this profile as an entity of type sigma tau; no function with output e is used. For any further arrow b:V->W, its value on x at coordinate b is the truth of F_{ba}(b^sigma x) on an arbitrary residual tuple from the domains at W. The naturality equation identifies this with b^tau(F_a(x)). Since the residual tuple is arbitrary at every b, all raw coordinates of the resulting relation equal those of F_a(x). Thus its entire operation component at a is F_a. At the identity its actual map is exactly F. Thus every external current set-function with relational output is represented.

For a current serial relation, choose a selecting set-function in ZFC and use this representation. This proves every current Functional Choice instance. Likewise every Boolean atom-swap involution of P(Out(R)) is represented as a current operation. Given distinct propositions, swap the actual atom with an atom in their symmetric difference. This proves S_pt.

Both objects have infinitely many individuals (N) and infinitely many propositions (the powerset of a countably infinite arrow set). Here is the direct Frege-cardinality argument, so the claim is stronger than each finite infinity-schema instance. Fix either object V and either carrier sigma=e or sigma=t. By extensional fullness, the higher-type property W whose current extension consists of exactly those cardinality entities Z such that every current property Y satisfying Z has finite actual extension is admitted. The zero cardinality belongs to W, since it holds exactly of empty current extensions. If Z belongs to W and Suc(Z) holds of Y, the definition of successor supplies x in Y such that Z holds of Y with x removed. That smaller extension is finite, so Y has finite extension. Thus W is successor-closed. The impredicative definition of FiniteCardinality forces every finite cardinality into W. Consequently no finite cardinality can hold of the universal property, whose extension is infinite. This proves the Axiom of Infinity at sigma. The argument works at both objects, so both e and t axioms hold necessarily. Their finite infinity schemata follow as well.

Finally BF_t fails. Let q be the singleton of (1_V,0) at the target V. It is in the image of no transport (h,n): the distinct target arrows (1_V,0) and (k,0) have the same composite with (h,n), so transported propositions cannot distinguish them. Take the admitted predicate X whose raw extension is all propositions at arrows into R, and all target propositions except q at arrows into V. Then every root p satisfies Box Xp, but at (h,0) the newly quantified q fails X. Thus forall p Box Xp holds and Box forall p Xp fails.

The model also has boxed Relational Choice, by fullness. It does not have boxed Functional Choice: the existing implication boxed FC -> C5 -> BF excludes that.

## Sources and scope

- Full action construction and C validity: `topics/classicism/groups/full-action-models.yaml`; source Bacon and Dorr, Classicism, draft 16 May 2023, sections 3.4-3.5, pp.55-61.
- Retract category: `topics/classicism/models/full-two-object-retract.yaml`; source Classicism, section 3.5, p.59, fifth paragraph and note 81.
- Full extension/infinity reasoning: `topics/classicism/arguments/infinitely-many-propositions.yaml` and the full-model construction above.
- The product construction, current-function extension proof, and P_sep full-action obstruction are new ordinary arguments in this lane, not claims already entered in the database or attributed to the source authors.
