# Zorn supplies admitted affine characters over H

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the arguments: `misc`, this note, §§2–7, unpaginated. The pre-existing Zorn principle is attributed separately in §§1 and 8.

The existing preorder version of Zorn, at the single type tt of proposition predicates, extends every admitted partial Boolean-group truth character. It therefore supplies infinite material XOR and biconditional separation from the corresponding group equations. The proof constructs admitted kernels and characters; it does not infer their admission from an external basis, external choice, or a full function domain.

## 1. Exact premises and the Zorn instance

Fix an admitted binary operation + on propositions. Assume the Boolean-group output equations: + is associative and commutative, has an identity 0, and x+x=0 for every x. These are universally quantified proposition-output identities, not identities between complete operations. The two applications take + to be a fixed XOR operation or a fixed biconditional operation with its H truth table. Their derived identities 0 are respectively false and true. Keep the chosen operation or abbreviation expansion fixed, as in [Term closure and affine branches](term-closure-and-affine-branches.md), §4.

Write L⊆K for ∀x(Lx→Kx), and write Subgroup(L) for

$$
L0\ \land\ \forall x,y\,(Lx\land Ly\to L(x+y)).
$$
Every predicate and operation quantified over is admitted. Subgroup inclusion is truth inclusion; mutual inclusion is never replaced by predicate identity.

Use [Zorn's Lemma](../../source/topics/classicism/principles/zorn-r.yaml) at σ=tt:

$$
\begin{aligned}
\forall R^{(tt)(tt)t}\bigl[&\operatorname{Preorder}(R)\land
\forall X^{(tt)t}\bigl(\operatorname{TotalOrder}(R,X)
  \to\exists U^{tt}\,\forall K^{tt}(XK\to R(K,U))\bigr)\\
&\to\exists K^{tt}\,\forall J^{tt}(R(K,J)\to R(J,K))\bigr].
\end{aligned}
\tag{1}
$$
Preorder means reflexive and transitive. TotalOrder includes transitivity, totality and actual antisymmetry on X, exactly as in [Background, order predicates](../../source/topics/classicism/background.md). The argument below proves the upper-bound condition even for all admitted comparable families, so the record's stronger chain restriction causes no difficulty.

The database's ambient C is not imported: formula (1) is an explicit additional premise over H. No recorded C equivalence between Zorn and other choice principles is used. In particular no Functional Choice, Plenitude, NI, ND, BF or Functionality is assumed.

## 2. An admitted maximal subgroup avoiding a prescribed element

Let L be an admitted subgroup and let d satisfy ¬Ld. Call a predicate K valid when

$$
V(K):=\operatorname{Subgroup}(K)\land L\subseteq K\land\neg Kd.
\tag{2}
$$
The given L is valid. On all proposition predicates define the admitted relation

$$
R(K,J):=\neg V(K)\lor\bigl(V(J)\land K\subseteq J\bigr).
\tag{3}
$$
It is a preorder. Invalid predicates are below everything. Among valid predicates it is inclusion, and a valid predicate is never below an invalid one. These observations directly verify reflexivity and transitivity; neither antisymmetry nor extensional identity of predicates is required.

For an admitted R-chain X, define the admitted union

$$
U(x):=Lx\lor\exists K^{tt}\,(XK\land V(K)\land Kx).
\tag{4}
$$
This is valid. It contains L and 0. To verify closure under +, two elements coming from valid members K,J of X lie together in whichever of K,J contains the other, by totality of R on X. If one comes from L, it lies in every valid member; if both come from L, use its closure. Every contributing subgroup omits d, so U omits d. Formula (4) also works for the empty chain or a chain containing only invalid predicates, in which case it is coextensive with L.

Every X-member K satisfies R(K,U): invalid K does so by the first disjunct of (3), and valid K is included in U. Thus (4) verifies the upper-bound premise of (1).

Zorn gives a maximal predicate K. It must be valid. Otherwise R(K,L) would hold and maximality would imply R(L,K), impossible because L is valid and K invalid. Its maximality therefore says

$$
\forall J\bigl[\operatorname{Subgroup}(J)\land K\subseteq J\land\neg Jd
\ \to\ J\subseteq K\bigr].
\tag{5}
$$
This is maximality up to coextension among admitted subgroups omitting d. It is exactly the conclusion needed; no quotient type of coextensive predicates is constructed.

## 3. Maximality gives two cosets and an admitted character

For any y, the admitted predicate

$$
K_y(x):=Kx\lor K(x+y)
\tag{6}
$$
is a subgroup containing K and y. If neither Ky nor K(y+d) held, (6) would omit d and strictly extend K, contrary to (5). Hence

$$
\forall x\,[Kx\lor K(x+d)].
\tag{7}
$$
The two alternatives are disjoint: their conjunction and subgroup closure would give Kd. They are the two cosets K and d+K.

Define the admitted truth test

$$
e(x):=\neg Kx.
\tag{8}
$$
It sends 0 to false and d to true, and it is false on L. Its truth values form an additive character:

$$
e(x+y)\ \leftrightarrow\
\bigl((ex\land\neg ey)\lor(\neg ex\land ey)\bigr).
\tag{9}
$$
For both inputs in K, their sum is in K. For exactly one input in K, membership of the sum in K would put the other input there too. For both outside K, (7) puts x+d and y+d in K, and their sum is x+y. This proves (9) in all four cases.

Thus H, the group equations and (1) prove the following **relative character theorem**: for every admitted subgroup L and every d outside it, an admitted truth character vanishes on L and is true at d. The character is the explicit term (8), rather than an externally specified linear functional assumed to belong to the model.

## 4. Extension of every admitted partial character

An admitted partial truth character consists of a subgroup L₀ and an operation e₀:tt such that e₀0 is false and (9), with e₀ in place of e, holds for all x,y in L₀. Its values outside L₀ are unrestricted. Extension means agreement in truth on L₀, not equality of its output objects.

If e₀ is false everywhere on L₀, the constant-false term extends it. Otherwise choose a single d in L₀ with e₀d true, and form the admitted kernel

$$
L(x):=L_0x\land\neg e_0x.
\tag{10}
$$
The partial character law makes L a subgroup omitting d. Apply §3, obtaining a full character e whose kernel contains L and omits d. For x in L₀:

- if e₀x is false, Lx, so ex is false;
- if e₀x is true, e₀(x+d) is false, so L(x+d). Since ed is true, (9) forces ex true.

Consequently ∀x(L₀x→(ex↔e₀x)). Every admitted partial truth character extends to an admitted character on the whole group.

This is an existence proof for each given partial character. Choosing d in its nontrivial case is ordinary existential elimination; the theorem does not select extensions uniformly over all partial characters.

## 5. Exact intrinsic maximality characterizations

The algebraic admission issue can be stated without a general order principle.

**Pointed maximality.** For every d≠0 there is an admitted subgroup K omitting d and satisfying (5).

Over H plus the Boolean-group equations, pointed maximality is equivalent to material separation for the corresponding affine operation. Forward, §§3 and 6 supply the separators, starting with the pointed maximal subgroup directly. Conversely, material separation of d and 0 supplies a truth character e with ed true. Its admitted kernel K(x):=¬ex omits d. If an admitted subgroup J includes K and has an element y outside K, then ey and ed are true, so e(y+d) is false. Hence y+d belongs to K and J, giving d in J. Thus any J still omitting d is included in K, which is (5).

For biconditional, convert a material observer E to the auxiliary character e:=λx.¬Ex; for XOR use e:=E. Material preservation forces E0 respectively true and false, so a separator of d from 0 has ed true in both cases.

There is also a stronger **relative maximality** principle: for every admitted subgroup L and d outside L, a K satisfying (2) and (5) exists. Over the group equations, the following are equivalent:

1. Relative maximality.
2. The relative character theorem of §3.
3. Every admitted partial truth character extends to the whole group.

The first implies the second by §3, and the second implies the third by §4. For the remaining implication, given L and d outside it, the admitted subgroup L′(x):=Lx∨L(x+d) has the partial character e₀(x):=L(x+d), false on L and true on d+L. The same four-coset calculation proves its character law. Extend e₀; its kernel gives (2) and (5) by the preceding argument.

Thus the relative theorem is an exact character-extension principle, while the unbased pointed version exactly captures character separation. No converse from ordinary separation to arbitrary partial-character extension, or from either specialized maximality principle to general Zorn, is asserted. Zorn at tt proves the relative version by §2.

## 6. XOR, biconditional, and endpoint alignment

Let S[R] mean that proposition identity is exactly agreement in truth under every admitted R-observer, as in [Truth profiles and connective reducts](truth-profiles-and-connective-reducts.md). Mat₊(E) requires E(x+y) to agree in truth with Ex+Ey. Let A(E):=E(Top) and Z(E):=¬E(Bottom).

For p≠q, d:=p+q is nonzero. On the admitted subgroup {0,d}, take the partial character e₀(x):=(x=d). Extend it by §4. Its values at p and q differ because ed is true. For XOR use E=e; for biconditional use E=λx.¬ex. The truth table in (9) gives the respective material preservation law. Equality implies agreement by H substitution.

Conversely, material separation forces the Boolean-group output equations by the truth-profile argument in [Term closure and affine branches](term-closure-and-affine-branches.md), §4. Therefore, **over H+Zorn at tt, material affine separation is equivalent to the corresponding Boolean-group equations**, separately for each chosen affine operation.

The same result has exact endpoint orientations. An extension can prescribe value one at any two nonzero c,d: if c=d, start on {0,d}; otherwise start on {0,c,d,c+d}, with the partial character true exactly at c and d. Its four-element addition table verifies the character law. Apply §4.

For XOR the group identity 0 is false, so Top≠0. Set c=Top to retain A while separating an arbitrary pair. Every material XOR observer rejects 0. If all separators also reject Bottom, separation identifies Bottom with 0; conversely that alignment makes Z automatic.

For biconditional the group identity 0 is true, so Bottom≠0. Set c=Bottom to make E=¬e reject Bottom while separating the pair. Every material biconditional observer accepts 0. Adding A forces Top=0 by separation, and that alignment conversely makes A automatic.

| Operation and qualification | Exact condition over H+Zorn at tt |
| --- | --- |
| XOR: Mat₊ or A∧Mat₊ | Boolean-group equations |
| XOR: Z∧Mat₊ or A∧Z∧Mat₊ | Boolean-group equations and Bottom=0 |
| Biconditional: Mat₊ or Z∧Mat₊ | Boolean-group equations |
| Biconditional: A∧Mat₊ or A∧Z∧Mat₊ | Boolean-group equations and Top=0 |

Here 0 is the derived unit of the indicated operation. These are endpoint truth conditions, not claims that the constructed material characters fix the original endpoint objects.

## 7. What Zorn supplies, and what still needs normalization

Zorn supplies admitted characters even when the proposition domain and the characters' images are internally infinite. It replaces the finite induction used in [Internally finite affine separation](finite-affine-separation.md). No internal or external finiteness is assumed here.

The new proof concludes material preservation. The output proposition objects in (8) need not form a two-element subgroup. With the separate premise Plenitude at input and output type t, [Plenitude normalization](plenitude-material-normalization.md), §§3 and 5, replaces every such material affine observer by a two-output pointwise affine observer with the same entire truth profile. Consequently all four rows of the table also characterize two-output pointwise affine separation over H+Zorn at tt+Plenitude at t,t.

Whole binary-operation preservation additionally follows from the relevant local Functionality instances, or from Functionality furnished by an independently assumed full typed separation scheme. Propositional material separation alone does not supply those instances. Likewise, no full typed separation scheme is inferred here merely from the propositional character theorem. The new maximality and extension statements do not contain object-language type quantification.

[Reversible affine normalization](partial-reversible-normalization.md), §§3–5, gives a second consequence of the supplied characters. Over H+Zorn at tt+Plenitude at t,t, the same group equations and endpoint alignments in §6 characterize separation by pointwise involutive affine observers fixing the required endpoints. With the stated local Functionality instances this is also equivalent to whole-operation involutive or reversible affine separation. At full relational scope, the corresponding characterization includes all Functionality, as required by typed factorization. Zorn supplies the material characters; the separate normalization constructs the involutions. The latter argument does not by itself infer character existence from the group equations.

This separates two admission tasks. Zorn at tt extends truth characters; Plenitude at t,t realizes a chosen two-output normalization. The results do not assert that either premise is necessary, that Zorn implies Plenitude over H, or that the bare group equations suffice for admitted infinite character separation without an additional argument.

## 8. Sources

The displayed preorder Zorn formulation is the existing [zorn-r record](../../source/topics/classicism/principles/zorn-r.yaml): Cian Dorr's suggestion of 8 October 2026, with Jonathan Lewin, “A Simple Proof of Zorn's Lemma,” *American Mathematical Monthly* 98 (1991), pp. 353–354, as its background source. The present proof uses that principle directly; it does not use the database's C proof from Transversal Choice or transfer its base assumptions to H.

The admitted-preorder construction, maximal-kernel argument, character extension and scoped equivalences in §§2–7 are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, direct source `misc`, this note, unpaginated. Plenitude's formulation and source are recorded in [the normalization note](plenitude-material-normalization.md), §§1 and 7.
