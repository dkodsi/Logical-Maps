# One countable join separates Maximalism from higher-type completeness

OpenAI Codex, 26 October 2026. Direct source: `misc`, numbered proof sections below, unpaginated.

**Pure Max(C) rules out one specific admitted countable join at the relational type ((et)t)t: the join of the singleton predicates of the current natural numbers.** Its existence is equivalent over C to numerical Barcan, and its value, if it exists, must be the numberhood predicate itself.

Consequently Max(C) is incompatible with Boolean Completeness at this one higher type. The [companion triangulation](completeness-triangulation.md), §3, uses existing cover models to show that even boxed BC_t, boxed ordinary BF and current full OS do not imply this join. The consistency of Max(C) + BC_t, with current BF or OS added, is not decided here.

Adding BC_t to Max(C) and numerical-type BF does have a sharper consequence: one current nonnumber can become a number in a possibility which keeps it distinct from every current number. With OS, one logical observer recognizes that number and rejects all its identities with current numbers simultaneously. Section 6 gives the precise modal scope.

## 1 The single family and its upper bounds

Put

```math
\nu=(et)t,\qquad N=\mathrm{FiniteCardinality}_e,
\qquad h_n:=\lambda m^\nu.(n=m).
```

The relevant family is the admitted property

```math
S(P):=\exists n^\nu\,(Nn\land P=h_n),
\qquad P:\nu t.
\tag{1}
```

It is countable in the database's internal relational sense: the admitted relation P=h_n with Nn associates each current member with its unique current numerical index. No operation selecting witnesses is needed.

Write J_N for the single current assertion that S has a least upper bound in the native algebraic order at nu t. Numerical Barcan is the single closed sentence

```math
\mathrm{BF}_N:=\forall X^{\nu t}\,
 \left[(\forall n^\nu\,(Nn\to\Box Xn))
 \to\Box\forall n^\nu\,(Nn\to Xn)\right].
\tag{2}
```

This quantifies over every admitted X, while its input quantifier is restricted to numberhood. It is distinct from the ordinary BF instance at nu.

For any admitted X, C gives the upper-bound characterization

```math
X\text{ bounds }S
\quad\Longleftrightarrow\quad
\forall n^\nu\,(Nn\to\Box Xn).
\tag{3}
```

Indeed h_n ≤ X means Box forall m(n=m implies Xm). Necessarily instantiating at n gives Box Xn. Conversely Box Xn and the necessitated equality-substitution theorem give that necessary universal implication. All these are uses of the native relational order, not merely current pointwise implications.

The [positive persistence theorem for numberhood](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/pure-possibility-implies-axiom-of-infinity-t.md), §1, Lemma 1, says Nn implies Box Nn. Equation (3) therefore shows that N is already an upper bound of S.

## 2 If the join exists, it is N

Suppose B is a current least upper bound of S. Since N is an upper bound,

```math
B\le_{\nu t}N.
\tag{4}
```

Equation (3) gives Box Bn for every current number n. Successors of current numbers are numbers, so also Box B(Suc n) for every current number n. Hence the admitted predicate

```math
B^+(n):=B(\mathrm{Suc}_e n)
```

is another upper bound of S. Leastness gives B ≤ B^+, or

```math
\Box\forall n^\nu\,[Bn\to B(\mathrm{Suc}_e n)].
\tag{5}
```

Also Box B(0) holds because 0 is a number. Induction is an unconditional theorem of C: any property containing 0 and closed under successor contains every number. Necessitate that theorem and apply it to these two boxed premises. This yields

```math
\Box\forall n^\nu\,(Nn\to Bn),
\quad\text{hence }N\le_{\nu t}B.
\tag{6}
```

Combining (4) and (6) gives the actual identity B=N. Neither the least-upper-bound assertion nor any optional completeness premise has been necessitated. This is the central step of Goodsell's [Lemma 8](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md), with the join assertion isolated from the full Countable Boolean Completeness schema.

## 3 Exact equivalence with numerical Barcan

Over C,

```math
J_N
\quad\Longleftrightarrow\quad
\mathrm{LUB}_{\nu t}(N,S)
\quad\Longleftrightarrow\quad
\mathrm{BF}_N.
\tag{7}
```

The first equivalence is §2 and the fact that N itself is an upper bound. If N is least, any X satisfying the antecedent of (2) is an upper bound by (3). Therefore N ≤ X, which is exactly the boxed conclusion of (2).

Conversely assume BF_N. For every upper bound X, equation (3) supplies the antecedent of (2), so N ≤ X. Since N is an upper bound, it is the least one. This completes (7).

Here the rigidity is that of *quantification restricted to numbers*. It is not the negative persistence of numberhood studied in [Numberhood rigidity and distinctness](numberhood-rigidity-and-distinctness.md). No implication from (7) to that negative-persistence condition, current modal 5, or C5 is asserted.

## 4 Arithmetic and the Maximalist boundary

In Goodsell's [proof of Theorem 9](../../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/countable-boolean-completeness-implies-necessity-of-arithmetic.md), the only use of Countable Boolean Completeness is Lemma 8, namely BF_N. The other finite-cardinality and arithmetic lemmas hold in C. Consequently J_N alone, added to C, gives at the base e every instance

```math
\Box(I_e\to A)\ \lor\ \Box(I_e\to\neg A)
\tag{8}
```

of Necessity of Arithmetic, where A is a closed arithmetical sentence and I_e has the source's fixed meaning. See Goodsell, *Arithmetic is Necessary*, draft of 5 June 2024, Definition 8 and Theorem 9, pp. 19–21, as located in the [recorded principle](../../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/necessity-of-arithmetic.yaml).

The [recorded incompatibility argument](../../../classicism-results-2026-10-24-v2/source/topics/classicism/results/possibility-and-necessity-of-arithmetic-incompatible.yaml), from Goodsell's Theorem 11 and note 14, pp. 24–26, now applies. C is recursively enumerable and C + I_e is consistent and interprets PA. Incompleteness supplies a closed arithmetical A such that I_e and A, and I_e and not A, are both C-consistent. Pure Max(C) makes both conjunctions possible, contradicting (8). The reference theory in both consistency tests is C, not C plus the new join assertion.

Thus

```math
C+\mathrm{Max}(C)\ \vdash\ \neg J_N,
\qquad
C+\mathrm{Max}(C)+\mathrm{BC}_{((et)t)t}
\ \vdash\ \bot.
\tag{9}
```

The first assertion is stronger and more specific than merely refuting completeness at that type: S is one fixed, explicitly defined countable family which must lack a join. Equivalently Max(C) forces an admitted X which every current number necessarily satisfies, while it is possible that some number does not satisfy X.

Boolean Completeness at nu t also entails BC_t over C. Given an admitted scalar family X, form its admitted family of constant predicates lambda m.p, with Xp. Let B be the higher-type join. Evaluation at the fixed object 0 makes B(0) an upper bound of X. Conversely every scalar upper bound u makes lambda m.u an upper bound of the constant-predicate family; leastness gives B ≤ lambda m.u, hence B(0) ≤ u. Thus B(0) is the scalar join. This makes BC_{((et)t)t} a strengthening of BC_t for the triangulation. The isolated assertion J_N is not claimed to imply BC_t.

No propositional BC, ordinary BF, observer separation, Choice, Zorn, or boxed completeness premise occurs in this contradiction. It places a precise higher-type upper boundary next to the still-unresolved scalar package C + Max(C) + BC_t.

## 5 Exactly when the pointwise scalar joins form an admitted predicate

For each m of type nu, define the admitted scalar family

```math
S_m(p):=\exists n^\nu\,(Nn\land p=(n=m)).
\tag{10}
```

Over C + BF_nu, the following is equivalent to J_N:

```math
\exists B^{\nu t}\,\forall m^\nu\,
       \mathrm{LUB}_t(Bm,S_m).
\tag{11}
```

First suppose (11). For each current number n, scalar upper-boundedness gives Box(n=m implies Bm) for every current m. Ordinary BF_nu collects these into Box forall m(n=m implies Bm), so h_n ≤ B. If U is any upper bound of all current h_n, then U(m) bounds S_m for every current m. Scalar leastness gives Box(Bm implies Um) at every m; BF_nu again collects these into B ≤ U. Thus B is the higher-type join of S, proving J_N.

Conversely J_N gives BF_N by §3, and the admitted predicate N represents the pointwise scalar joins. Fix m. Positive numberhood persistence makes N(m) an upper bound of S_m. If u is any scalar upper bound, every current number n satisfies Box(n=m implies u). Apply BF_N to the admitted predicate X(n):=(n=m implies u). Its conclusion, instantiated at n=m inside the box, gives Box(Nm implies u). Hence N(m) ≤ u, proving that N(m) is the scalar join. This direction needs no ordinary BF and no BC_t: J_N itself supplies these particular scalar joins.

Under BC_t, the admitted relation R(m,u):=LUB_t(u,S_m) is current, total and single-valued. Consequently C + Max(C) + BC_t + BF_nu forces this specific relation to have **no admitted representing operation**. All its scalar values exist uniquely, but assembling those exact values into one admitted predicate would give (11), and hence the forbidden join J_N. This is an exact equivalence about the specified family, rather than an inference from current coextension to identity. In particular it applies to the full OS package, since full OS supplies BF_nu. No general choice or nonrepresentation principle is being inferred from an unspecified family.

## 6 A possible number distinct from every current number

Retain

```math
\Pi:=\forall n^\nu\,[Nn\to\Diamond a_n],
\qquad a_n=(\mathrm{Suc}_e n)(\lambda x^e.\top).
```

**Theorem.** C + Max(C) + BC_t + BF_nu implies

```math
\exists m^\nu\exists r^t\,\left[
 \neg Nm\land\Diamond r
 \land\Box\bigl(r\to(\Pi\land Nm)\bigr)
 \land\forall n^\nu\bigl(Nn\to\Box(r\to m\ne n)\bigr)
\right].
\tag{12}
```

Thus the same possible condition r makes m a number while excluding its identity with each current number. Every guard Nn in the last conjunct is outside the box. This is not a claim that the possible numerical domain consists of the current numbers.

For each current m, BC_t supplies the unique scalar join u_m of S_m from (10). This notation specifies values one at a time, not an admitted operation. Suppose, for contradiction, that

```math
\Pi\land Nm\le u_m\qquad\text{for every current }m.
\tag{13}
```

We derive the Pi-relative numerical Barcan principle

```math
\forall X^{\nu t}\,
 \left[\forall n(Nn\to\Box(\Pi\to Xn))
 \to\Box\bigl(\Pi\to\forall n(Nn\to Xn)\bigr)\right].
\tag{14}
```

Fix X satisfying its antecedent and fix any m. For each current number n, the antecedent and equality substitution give

```math
\Pi\land(n=m)\le Xm.
```

Finite meet distributes over the existing join u_m. Consequently Pi and u_m together entail Xm. Assumption (13) now gives Pi and Nm together entail Xm. In native modal notation this is Box(Pi and Nm implies Xm). Generalizing m and applying ordinary BF_nu collects these pointwise boxes into the boxed universal implication in (14).

The previously proved [Pi-relative arithmetic argument](logical-observers-and-numberhood.md), §1, shows that (14) contradicts pure Max(C). Its arithmetic induction uses the C theorem Pi implies I_e and Goodsell's atomic persistence lemmas; its metatheoretic last step uses Gödel–Rosser for the consistent recursively enumerable theory C + Pi. Both opposing pure arithmetic conjunctions remain C-consistent, so the reference theory in Max is unchanged. No additional BF or completeness premise is hidden in that arithmetic step.

Therefore (13) fails at some m. Choose its scalar join u_m and put

```math
r:=\Pi\land Nm\land\neg u_m.
\tag{15}
```

It is nonzero. For every current number n, (n=m) ≤ u_m by its upper-bound property, so r ≤ not(m=n). Also r ≤ Pi and Nm. These give the boxed clauses of (12). Finally m cannot be a current number: otherwise S_m contains the Top proposition (m=m), forcing u_m=Top and r=Bottom. Hence not Nm, completing the proof. The argument chooses u_m only after fixing m and never assembles the joins into an admitted function.

**One-observer consequence.** Full OS supplies BF_nu. Fix the same m,r from (12), and fix any finite qualification list Delta. Separation of r from Bottom supplies a Good_Delta observer E with E(r) true. Boolean preservation carries the three algebraic bounds on r to give, simultaneously,

```math
E\Pi,\qquad E(Nm),\qquad
\forall n^\nu\,[Nn\to\neg E(m=n)].
\tag{16}
```

The same m can serve for every finite external list; E may vary with the list. The expression E(m=n) is E applied to the native identity proposition, not an assertion that E fixes identity or numberhood. No acceptance of the number-set code unit b is proved, and no nonprincipal reader of that code algebra is inferred.
