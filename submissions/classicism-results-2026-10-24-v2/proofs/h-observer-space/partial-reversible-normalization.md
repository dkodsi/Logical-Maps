# Reversible negation and affine separation under Plenitude

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§2–5, unpaginated. Plenitude and the earlier representation results are attributed in §6.

For negation alone, or for either affine operation separately, an explicit admission principle removes the extra cost of reversibility. Under Plenitude at t,t, materially separating observers can be replaced by pointwise involutions preserving the chosen operation. Local Functionality upgrades the equations to identities of whole operations; full relational separation supplies that Functionality itself. These conclusions are specific to the named partial signatures.

The replacements need only distinguish the specified pair. They do not retain the original observer's entire truth profile. Nor do they preserve other connectives or quantifiers that happen to be preserved by that observer.

## 1. Premises and preservation tiers

Use H, the fixed Top and Bottom abbreviations T,B, and the exact single instance Plen_{t,t} from [Plenitude normalization](plenitude-material-normalization.md), §1. It says that every admitted, currently total and single-valued relation from propositions to propositions has an admitted operation representing it. This formula is an additional H premise; its database record's C background is not imported.

For a fixed operation f, write Mat_f and Pt_f for material and pointwise preservation. Define a **pointwise involution** by

```math
\mathrm{Invol}_{\mathrm{pt}}(E):=
\forall p\,[E(Ep)=p].
\tag{1}
```

The whole-operation condition is instead E∘E=I. Equation (1) does not imply that condition over bare H. Likewise, pointwise preservation is not identified with identity of the complete composite operations.

An endpoint orientation O is one of no condition, A(E):=ET, Z(E):=¬EB, or A∧Z. Write Fix(O) for fixing the endpoint objects mentioned by O; the empty orientation gives no condition. Every fixed endpoint has its correct H truth value, so Fix(O) implies O.

We use the existing propositional separation formula S[K]. FullSep[K] is its full relational schema, with no object-language type quantifier.

## 2. Negation: admitted flips of single pairs

**Theorem 1.** Under H+Plen_{t,t}, for every orientation O,

```math
S[O\land\mathrm{Mat}_N]
\quad\longleftrightarrow\quad
S[\mathrm{Fix}(O)\land\mathrm{Pt}_N
       \land\mathrm{Invol}_{\mathrm{pt}}].
\tag{2}
```

Without both endpoint conditions these principles are equivalent to the double-negation identity DN:=∀p(¬¬p=p). With both conditions they are equivalent to DN together with B=¬T.

The material characterization and endpoint alignment are [Truth profiles](truth-profiles-and-connective-reducts.md), §§4 and 6. For completeness, material negation separation makes p and ¬¬p have the same profile, hence identifies them. If every eligible observer accepts T and rejects B, it accepts ¬B, so separation identifies T=¬B and DN gives B=¬T. The converses for material separation are proved there by admitted formula tests.

It remains to construct the stronger witnesses under these output identities. DN and the H negation truth clause partition the propositions into pairs {r,¬r}, with precisely one true member of each pair. Fix a pair and use Plenitude on the admitted functional relation

```math
\begin{aligned}
U_r(x,y):={}&((x=r\lor x=\neg r)\land y=\neg x)\\
&\lor(\neg(x=r\lor x=\neg r)\land y=x).
\end{aligned}
\tag{3}
```

Ordinary bivalence determines one branch, and each branch specifies one proposition object. Thus U_r is total and single-valued in H, and Plenitude gives an admitted F_r satisfying it. This operation exchanges r and ¬r and fixes every other proposition.

The pair is closed under negation. On it, both F_r(¬x) and ¬F_r(x) equal x; off it, both equal ¬x. Thus F_r preserves negation pointwise. Applying the flip twice returns every input, proving (1).

Take distinct p,q. If their truth values differ, identity separates them and satisfies every required fixing condition. Otherwise p,q belong to different negation pairs. If there is no endpoint condition, flip p's pair. With A only, choose whichever of p,q lies outside T's pair and flip that pair; such a choice exists because two distinct members of one pair cannot have the same truth value. With Z only use B's pair instead. With both conditions B=¬T makes the two protected endpoint pairs the same, and the same choice works. The flip changes the truth of precisely one member of p,q and fixes the required endpoints. This proves the forward implication in (2). The converse follows by forgetting the extra qualifications.

For no endpoint condition one may still choose the witnesses to fix T, or instead to fix B. Requiring both endpoint objects fixed adds exactly the stated alignment, rather than following from DN alone.

## 3. Affine separation: involutions fixing a chosen opposite-unit proposition

Fix one admitted binary operation + with the H truth table of XOR or biconditional. Its syntactic expansion is held fixed throughout. Do not identify the two operations or add preservation of an unmentioned primitive. Material + separation gives the elementary abelian 2-group identities BG(+), by [Term closure and affine branches](term-closure-and-affine-branches.md), §4. Write 0 for its group identity; every element satisfies x+x=0.

For the argument only, use the auxiliary formula

```math
\tau(x):=
\begin{cases}
x,&\text{for XOR},\\
\neg x,&\text{for biconditional}.
\end{cases}
\tag{4}
```

Here τ is a formula giving a truth value, not a newly postulated two-element object type. It satisfies τ(0) false and the material XOR law for +. Choose any a with τ(a) true. Such an a exists: T works for XOR, and B for biconditional.

**Theorem 2.** Under H+Plen_{t,t}, for every such a,

```math
S[\mathrm{Mat}_{+}]
\quad\longleftrightarrow\quad
S[\mathrm{Pt}_{+}\land\mathrm{Invol}_{\mathrm{pt}}
       \land Ea=a].
\tag{5}
```

The proof is a pairwise construction. Suppose p≠q and put d=p+q, so d≠0 by the group laws. If τ(d) is true, p,q already differ in truth; identity is a witness fixing a.

Suppose instead τ(d) is false. Material separation of d from 0 gives E with τ(Ed) true. Indeed the material homomorphism law forces τ(E0) false, so a distinguishing observer must give the opposite truth at d. Put χ(x):=τ(Ex). This admitted formula is a material XOR character and χ(d) is true.

Arrange additionally that χ(a) is false. If it is already false, keep χ. Otherwise replace it by the truth-XOR of χ and τ. The replacement is still a character, is false at a because τ(a) is true, and stays true at d because τ(d) is false. This operation is composition of admitted formulas; no object-valued conditional or choice function has yet been assumed.

Plenitude now gives an admitted L with

```math
Lx=
\begin{cases}
a,&\chi(x),\\
0,&\neg\chi(x).
\end{cases}
\tag{6}
```

More formally apply it to (χ(x)∧y=a)∨(¬χ(x)∧y=0), which is total and single-valued by H. The pair {0,a} is a two-element subgroup. Its exact group table, together with the character law, proves

```math
L(x+y)=Lx+Ly,\qquad L0=0,\qquad La=0.
\tag{7}
```

Define the admitted operation

```math
Jx:=x+Lx.
\tag{8}
```

Commutativity, associativity and (7) show J(x+y)=Jx+Jy. Also L(Lx)=0, because Lx is either 0 or a. Consequently

```math
J(Jx)=x+Lx+L(x+Lx)
     =x+Lx+Lx+L(Lx)=x.
\tag{9}
```

Thus J is a pointwise involutive group homomorphism and Ja=a. Since χ(d) is true, Jd=d+a, whose τ-value is true. Homomorphism preservation gives Jd=Jp+Jq, so Jp,Jq differ in truth. This is the required witness. The reverse implication in (5) merely forgets qualifications.

The construction is often called a transvection: a homomorphism with square zero is added to identity. Equations (6)–(9), rather than that terminology, provide the internal admitted witness. No basis, maximal subgroup, global character choice or finiteness is used.

## 4. Exact endpoint variants

The preceding theorem strengthens all the usual affine orientations:

```math
S[O\land\mathrm{Mat}_{+}]
\quad\longleftrightarrow\quad
S[\mathrm{Fix}(O)\land\mathrm{Pt}_{+}
       \land\mathrm{Invol}_{\mathrm{pt}}].
\tag{10}
```

For XOR choose a=T. The constructed witnesses always fix T. If Z is present, the existing material endpoint theorem identifies B=0: every material affine observer rejects both B and 0. Group homomorphisms fix 0, so they then fix B as well. No additional equation is needed for A alone.

For biconditional choose a=B. The witnesses always fix B. If A is present, separation identifies T=0 because every material affine observer accepts the group unit; the witnesses then fix T too. No additional equation is needed for Z alone. Conversely, fixing an endpoint implies the corresponding truth condition, so the right side of (10) implies the left in every case.

These arguments also recover the exact structural contribution of orientation. Over the stated Plenitude premise, A adds no strength to XOR separation, while Z adds B=0. Z adds no strength to biconditional separation, while A adds T=0. They do not identify the two group structures or supply missing material characters from group identities alone.

## 5. Whole identities, full types and limits

For negation, Fun_{t,t} upgrades both pointwise negation preservation and (1) to their whole-operation identities. For the binary affine operation, whole preservation additionally uses Fun_{t,tt}: first identify the inner unary maps for each first argument, then the outer maps. These are explicit local premises at propositional scope.

Therefore, under those local Functionality instances, each right side of (2) and (10) can use whole-operation preservation and E∘E=I. The observer is its own admitted inverse, qualified for exactly the same operation and endpoint conditions. Equivalently one can permit arbitrary qualified two-sided inverses, since that class lies between these involutions and the original material observers.

At full relational scope, [typed factorization](typed-separation-and-classicism.md), §2, gives FullSep[K] iff S[K]+Functionality. Applying (2) or (10), and then the Functionality upgrades, proves that the full typed material, pointwise, whole-operation and reversible versions coincide under Plen_{t,t} for these signatures. Unlike the profile-preserving normalization of the earlier Plenitude note, this use of factorization is necessary: the involution constructed for one pair need not preserve an earlier observer's profile on every proposition.

The conclusion concerns negation alone and each separate affine operation. It does not extend to conjunction merely from Plenitude. The full-function six-element model in [Reversible meet characterization](reversible-meet-characterization.md), §6, admits every current function, hence Plen_{t,t}, yet has ordinary strong accepting/rejecting meet separation and fails reversible meet separation. Its asymmetric atom order obstructs the latter. No analogous collapse for the complete logical signature under Plenitude is asserted here.

No claim is made that BG(+) alone provides material affine separation on infinite domains. This note starts with that separation and supplies reversible witnesses; intrinsic character existence is a separate question. Nor are additional negation, lattice, quantifier, equality or fixed-parameter conditions automatically retained by the affine construction.

There are exact extensions when the additional operations have a proved compatibility identity. [Negation and affine compatibility](negation-affine-compatibility.md), §§2–7, treats N together with either affine operation and compatible XOR/biconditional pairs. Its witnesses fix the distinguished translation element, so they preserve the linked signature; their endpoint alignments and Functionality premises remain explicit.

## 6. Sources

The Plenitude formula is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.3, pp. 31–33, as recorded in [Plenitude](../../source/topics/classicism/principles/plenitude-r.yaml). The general admission and normalization use of that formula is [Plenitude normalization](plenitude-material-normalization.md), §§1–6, direct source `misc`, unpaginated.

The negation characterization and endpoint equations are [Truth profiles](truth-profiles-and-connective-reducts.md), §§4 and 6; affine output identities are [Term closure and affine branches](term-closure-and-affine-branches.md), §4. Those earlier local arguments have direct source `misc` and unpaginated section locators. The finite affine comparisons are separately proved in [Finite affine normalization](finite-affine-normalization.md); their finiteness premises are not used here.

The finite-pair flips, affine involutions, endpoint-fixing refinements and their scope consequences in §§2–5 are new ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, direct source `misc`, unpaginated.
