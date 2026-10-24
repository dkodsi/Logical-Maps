# Finite affine separation by two-output homomorphisms

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–7, unpaginated.

Internal Frege finiteness closes the gap between material and pointwise affine separation. If the whole proposition domain is internally finite, the Boolean-group equations suffice to construct separating, admitted, two-output group homomorphisms. More generally, an individual material affine observer with internally finite image can be replaced by a two-output pointwise observer with the same entire truth profile, even on an infinite domain. No identity bivalence, Necessity of Distinctness, Choice, C, or Functionality is needed for these pointwise conclusions.

## 1. Exact statement and scope

Use the fixed relational type system and the internal formula Fin_t(All) from [Internally finite affine separation](finite-affine-separation.md), §1. It means that the entire proposition domain has a Frege finite cardinality. It does not supply an external enumeration or a standard finite bound.

Fix an actual binary propositional operation + whose H truth table is either XOR or biconditional. The choice of its syntactic expansion remains fixed throughout, as in [Term closure and affine branches](term-closure-and-affine-branches.md), §1. Let BG(+) be the pointwise equations of an elementary abelian 2-group: associativity, commutativity, a common identity 0, and x+x=0. The symbol 0 denotes the group identity, which is false in the XOR case and true in the biconditional case; it is not assumed to be the fixed Bottom or Top.

Write Mat_+(E) for material preservation and Pt_+(E) for

$$
\forall x,y\; E(x+y)=Ex+Ey.
$$

Two(E) means that E has at most two actual output objects. Separation S uses agreement in truth, as in the [atlas notation](README.md).

**Theorem.** Over H+Fin_t(All),

$$
\mathrm{BG}(+)
\quad\longleftrightarrow\quad S[\mathrm{Mat}_+]
\quad\longleftrightarrow\quad S[\mathrm{Two}\land\mathrm{Pt}_+].
\tag{1}
$$

Consequently material and pointwise separation coincide for each separate affine operation in this finite region. Adding the local Functionality instances Fun_(t,t) and Fun_(t,tt) gives whole-operation separation as well. At full relational separation scope, the same equivalence holds with precisely the explicit Functionality schema on the structural side.

The witnesses have the two outputs 0,c for a suitable c≠0. They are not claimed to take the fixed values Top and Bottom, to fix those objects, or to preserve primitive negation, conjunction, disjunction, or quantifiers.

There is also an exact reduction without finiteness of the proposition domain. For O equal to no endpoint condition, A, Z or A∧Z, over bare H,

$$
\boxed{
S[O\land\mathrm{FinIm}\land\mathrm{Mat}_+]
\quad\longleftrightarrow\quad
S[O\land\mathrm{Two}\land\mathrm{Pt}_+].}
\tag{8}
$$

FinIm is internal Frege finiteness of the admitted image predicate, as in [Finite-image material normalization](finite-image-material-normalization.md), §1. Section 6 proves (8), including the stronger individual-observer normalization under BG(+). Full relational scope again makes the pointwise and whole-operation versions equivalent. This does not settle unrestricted affine separation on an infinite domain.

## 2. A subgroup and an invariant truth test

Assume BG(+) and fix d≠0. We construct an admitted subgroup K avoiding d and an admitted operation A:tt satisfying

$$
\forall x\;(Ax\leftrightarrow Kx),
\qquad
\forall k,x\;(Kk\to A(x+k)=Ax).
\tag{2}
$$

The first condition concerns truth; the second is a pointwise identity. Initially take

$$
K(x):=(x=0),\qquad A(x):=(x=0).
$$

This subgroup avoids d, and (2) holds by substitution. No assumption is made about the output object of a true or false identity judgment.

Suppose y lies outside both K and d+K. Define

$$
K'(x):=Kx\lor K(x+y).
\tag{3}
$$

The two cosets in (3) are disjoint. Their union is a subgroup, contains K and y, and still avoids d: if d belonged to y+K, then y would belong to d+K.

Define an admitted operation by the appropriate displayed term:

$$
A'(x):=
\begin{cases}
Ax+A(x+y),&\text{XOR truth table},\\
\neg\bigl(Ax+A(x+y)\bigr),&\text{biconditional truth table}.
\end{cases}
\tag{4}
$$

These are two externally specified constructions, not an object-language case operator. In either construction A'(x) has the XOR truth value of Ax and A(x+y). Since those tests cannot both be true, A' is true exactly on K'.

For k∈K, both summands in (4) are unchanged as objects when x is replaced by x+k. Translation by y exchanges the summands, because y+y=0. Commutativity therefore makes their sum identical, and in the biconditional construction equality congruence preserves this identity after negation. Thus A' is invariant under every translation by K'. This argument assumes no preservation or algebraic identity for primitive negation.

We have proved an extension step: whenever y is not yet covered by K∪(d+K), enlarge K and its invariant truth test so that y is covered, while retaining every previously covered input.

## 3. Internal finite induction covers the domain

Let Admissible_d(K,A) express the subgroup, avoidance and two conditions in (2). These are finite formulas in the admitted relational language. Define the property of cardinality objects

$$
W(Z):=\forall U\left[ZU\to
\exists K,A\left(
\mathrm{Admissible}_d(K,A)
\land\forall x\bigl(Ux\to(Kx\lor K(x+d))\bigr)
\right)\right].
\tag{5}
$$

The zero cardinality satisfies W: use the initial subgroup and test in §2, since its U is empty. For the successor step, suppose Suc(Z)U and choose its witness y. By the defining Frege successor formula,

$$
Z(\lambda x.Ux\land x\ne y).
$$

Apply W(Z) to that deletion predicate. If y is already in K∪(d+K), retain the witnesses. Otherwise use (3)–(4). The resulting witnesses cover every member of U and establish W(Suc(Z)).

Frege induction yields W(Z) for every internally finite cardinality Z. Apply it to a witness Z with Z(All). We obtain

$$
\forall x\;(Kx\lor K(x+d)),\qquad \neg Kd.
\tag{6}
$$

No uniform selection of witnesses over cardinalities or inputs occurs. At each successor step only the existential witnesses of that step are used. The operations in (3)–(5) are explicit lambda terms, so this proof does not presume admission of an externally chosen basis, sum, character, or enumeration.

## 4. The two-output homomorphism

Put u:=A0 and v:=Ad. Then u is true and v is false, hence u≠v. Translation invariance and (6) give the exact output table

$$
Ax=
\begin{cases}
u,&Kx,\\
v,&K(x+d).
\end{cases}
$$

Define F(x):=Ax+u and c:=v+u. The two outputs of F are 0 and c, and c≠0 by group cancellation. Its kernel is K; the other coset is d+K. Adding two members of the other coset returns to K, while adding a K-member leaves coset membership unchanged. Because c+c=0, the four coset cases give

$$
F(x+y)=Fx+Fy.
\tag{7}
$$

In the XOR case 0 is false and c is true. In the biconditional case 0 is true and c is false. Thus F0 and Fd differ in truth in both cases.

For any p≠q use d:=p+q, which is nonzero. Equation (7) gives Fp+Fq=Fd=c≠0; since Fp,Fq belong to {0,c}, they are the two different outputs and differ in truth. This proves separation by two-output pointwise homomorphisms.

Conversely pointwise preservation implies material preservation by H substitution. Material affine separation gives the Boolean-group equations by the faithful truth-profile calculation in [the affine branch](term-closure-and-affine-branches.md), §4, or [the earlier finite note](finite-affine-separation.md), §1. This proves (1).

## 5. Endpoint truth orientations

The same construction can arrange that two prescribed nonzero elements d and a both lie outside K. If a=d, there is nothing to change. Otherwise a+d lies outside the initial subgroup {0} and its d-coset {d}; perform the extension step once with y:=a+d. The resulting K contains a+d and avoids d. Every later extension retains those two properties, which force a∉K. Carry out (5) with this strengthened initial condition and the additional requirement K(a+d).

For XOR take a:=Top, which is nonzero because Top is true and the group identity is false. The resulting F accepts Top. Every group homomorphism rejects its identity 0. Hence rejection of Bottom can be added to separation exactly when Bottom=0, by the same separation argument as in the earlier material theorem.

For biconditional take a:=Bottom, which differs from its true group identity. The resulting F rejects Bottom. Every group homomorphism accepts its identity. Acceptance of Top can be added exactly when Top=0.

Thus the four endpoint variants in [the earlier finite note](finite-affine-separation.md), §5, remain exact after replacing material preservation by two-output pointwise preservation:

| Operation | Extra condition for no orientation | Acceptance A | Rejection Z | A and Z |
|---|---|---|---|---|
| XOR | None | None | Bottom=0 | Bottom=0 |
| Biconditional | None | Top=0 | None | Top=0 |

These are truth conditions on the endpoint outputs; no endpoint fixing follows unless separately proved.

## 6. Finite images suffice for profile-preserving normalization

Assume BG(+), and let E be any admitted observer with FinIm(E). We first construct a two-output observer F with

$$
\forall p\;(Fp\leftrightarrow Ep).
\tag{9}
$$

If E is materially + preserving, the construction will make F pointwise + preserving. The image of E need not be a subgroup, and no closure of that image under + is assumed.

For compact notation define the admitted predicate

$$
\tau(x):=
\begin{cases}
x,&\text{XOR truth table},\\
\neg x,&\text{biconditional truth table}.
\end{cases}
$$

This is two externally specified choices of a term. It is a truth character of the ambient group: τ0 is false, and τ(x+y) has the XOR truth value of τx and τy. No pointwise preservation by τ is asserted. Fix d with τd true: take Top for XOR and Bottom for biconditional. Thus d≠0. Write ker τ for the admitted predicate λx.¬τx.

We strengthen the invariant-test induction in §3. Let B_τ(K,A) express that K is a subgroup, K⊆ker τ, A is truth-characteristic of K, and A is pointwise invariant under every K translation as in (2). Define

$$
\begin{aligned}
\mathrm{Cover}_\tau(U,K):=\forall x\bigl[Ux\to
&((\neg\tau x\to Kx)\\
&\land(\tau x\to K(x+d)))\bigr],
\end{aligned}
$$

and the admitted induction property

$$
W_\tau(Z):=\forall U\left[ZU\to
\exists K,A\bigl(B_\tau(K,A)\land
\mathrm{Cover}_\tau(U,K)\bigr)\right].
\tag{10}
$$

For zero, use K(x):=(x=0) and A(x):=(x=0). For a successor witness y, apply the induction hypothesis to the exact deletion predicate λx.Ux∧x≠y. If τy is false put z:=y; if τy is true put z:=y+d. This is an ordinary proof by cases selecting one existing proposition in each case, not an assumed admitted conditional operation. In either case τz is false. If z∈K, retain K,A. Otherwise z lies outside K∪(d+K): membership in d+K would make τz true because K⊆ker τ. Apply the extension (3)–(4) with z in place of y.

The enlarged subgroup remains within ker τ, since both K and z have τ value false. It retains the old cover and covers y in the required coset. Its new test remains characteristic and translation-invariant by §2. Hence W_τ is successor-closed. Frege induction proves (10) for every internally finite cardinality; it requires neither an enumeration nor a function choosing extensions.

Apply (10) to the actual image predicate Im(E)(x):=∃p(Ep=x), using FinIm(E). Put u:=A0 and v:=Ad. Then u is true and v is false: 0∈K, whereas τd is true and K⊆ker τ. Every output Ep satisfies

$$
A(Ep)=
\begin{cases}
u,&\neg\tau(Ep),\\
v,&\tau(Ep).
\end{cases}
\tag{11}
$$

Indeed, in the first case Ep∈K, so translation invariance gives A(Ep)=A0. In the second Ep+d∈K, so invariance applied at d gives A(Ep)=Ad. These are identities of output objects.

Define the admitted operation

$$
F(p):=A(Ep)+u,\qquad c:=v+u.
\tag{12}
$$

It takes the values 0 and c, and c≠0. For XOR, 0 is false and c is true; for biconditional, 0 is true and c is false. By the definition of τ, (11) therefore gives exactly (9). This includes constant truth profiles; the construction does not require both truth values to occur in Im(E).

Now suppose E is materially + preserving. The two output objects 0,c form a subgroup with c+c=0 and have the correct opposite truth values. Material preservation and (9) give F(x+y) and Fx+Fy the same truth value. Both lie in {0,c}; its two members differ in truth, so they are equal. Thus F is pointwise + preserving. Since (9) holds at every input, every A/Z orientation is retained.

For (8), finite-image material separation first supplies BG(+) by the material truth-profile theorem. Replacing each separator by (12) proves two-output pointwise separation. Conversely Two(F) implies FinIm(F) over H: choose an actual output a=F(Top); if it is the only one, deletion witnesses a singleton image, and otherwise choose a second distinct actual output b and delete a then b. The at-most-two bound leaves the empty predicate. The two corresponding Frege successors are finite by the defining induction clause. This is the same internal singleton/pair proof as [Finite-image material normalization](finite-image-material-normalization.md), §5. Pointwise preservation implies material preservation, giving the reverse implication.

The replacement keeps the whole current truth profile, so the proof of (8) also applies at each relational separation scope. At full typed scope, Functionality supplies the whole-operation law as described next. No conclusion about primitive negation or other unlisted operations is drawn.

## 7. Whole operations, full types, and sources

The proof establishes (7) pointwise. Fun_(t,t) first identifies the y-abstractions at each x; Fun_(t,tt) then identifies the x-abstractions. This gives the whole composite preservation identity without invoking C.

The general [typed factorization theorem](typed-separation-and-classicism.md), §2, identifies full relational separation with propositional separation plus the Functionality schema. Therefore over H+Fin_t(All), full relational material affine separation, full relational pointwise affine separation, and full relational whole-operation affine separation are all equivalent to BG(+) plus Functionality, with the table's endpoint alignments where requested. One finite group witness is supplied for each separation instance; no quantifier over types or simultaneous observer schema is introduced.

The Frege definitions and their scope are from [Background, Notation](../../source/topics/classicism/background.md). The earlier material theorem and the group consequences of truth profiles are the linked research notes. The invariant subgroup-test construction and the stronger conclusions here are new, direct source `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, §§2–7, unpaginated. This note strengthens the earlier finite result; its concluding limitation about pointwise affine separation is superseded under finite-domain or finite-image hypotheses. General infinite affine representation without such an admission or normalization hypothesis remains unresolved.
