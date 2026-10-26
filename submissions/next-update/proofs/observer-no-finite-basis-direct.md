# OS and finite axiomatizations: a direct Boolean-algebra proof

For each finite type-order bound, this construction gives two C models with the same bounded-order reduct. One satisfies full OS; the other fails BF at a higher type. Thus OS has no finite equivalent axiomatization over C, nor an equivalent axiom set of uniformly bounded elaborated type order. The same holds for every theory between C + BF and C + OS.

The construction takes place in ZFC. It uses a complete Boolean algebra, a typed Henkin quotient and [coherent profiles](observer-term-closed-profile-models.md). The [alternative forcing proof](observer-no-finite-basis.md) retains its separate comparison with a specified ground standard model. Here both comparison models instead use the same quotient Henkin hierarchy.

## 1. A distributive Boolean algebra with independent columns

Fix $`n<\omega`$, put $`\mu=\beth_n`$ and let $`\kappa=\mu^+`$. Let $`P`$ consist of partial functions from $`\kappa\times\kappa`$ to $`2`$ with domain of size less than $`\kappa`$, ordered by extension. The first coordinate indexes columns.

On $`\Omega=2^{\kappa\times\kappa}`$, use the topology with basic clopen sets

```math
[p]=\{x\in\Omega:p\subseteq x\}\qquad(p\in P).
```

These sets can specify infinitely many entries, provided there are fewer than $`\kappa`$. Let $`B=\mathrm{RO}(\Omega)`$. The basic conditions are dense in this complete Boolean algebra; two have nonzero meet exactly when they are compatible. Their union then gives a common extension. Write $`b_{i,\alpha}`$ for the Boolean value of assigning 1 at $`(i,\alpha)`$. Column permutations induce automorphisms of $`B`$ and permute these values accordingly.

**Distributivity lemma.** Any family of fewer than $`\kappa`$ maximal antichains of $`B`$ has a common refining maximal antichain.

Start below any nonzero Boolean element with a basic condition. For each antichain, choose a member compatible with the current condition and strengthen into that member. At limit stages take unions. Regularity of $`\kappa`$ keeps each union a condition. The resulting common refinements are dense; choose a maximal antichain among them. This proves the lemma directly.

## 2. The Boolean-valued typed hierarchy

Define carriers $`X_\sigma`$ with Boolean-valued equalities $`d_\sigma`$. At $`e`$, take all $`B`$-partitions $`(a_m)_{m\in\omega}`$ of 1 and set

```math
d_e((a_m),(c_m))=\bigvee_{m\in\omega}(a_m\wedge c_m).
```

The representative of a ground individual $`m`$ has value 1 at $`m`$ and 0 elsewhere. Set $`X_t=B`$, with $`d_t(b,c)=(b\leftrightarrow c)`$. For every admitted arrow, take all Boolean-extensional maps:

```math
X_{\sigma\tau}=
\{f:X_\sigma\to X_\tau:
d_\sigma(x,y)\le d_\tau(f(x),f(y))\text{ for all }x,y\},
```

```math
d_{\sigma\tau}(f,g)=\bigwedge_{x\in X_\sigma}d_\tau(f(x),g(x)).
```

Each carrier admits mixing: for a Boolean partition $`(a_j)`$ and objects $`x_j`$ there is $`x`$ such that $`a_j\le d_\sigma(x,x_j)`$ for every $`j`$. At $`e`$ mix coordinatewise; at $`t`$ use $`\bigvee_j(a_j\wedge x_j)`$; at arrows mix outputs pointwise. Pointwise mixing preserves Boolean extensionality.

Application is evaluation, Boolean operations are those of $`B`$, and quantification is

```math
Q_\sigma(f)=\bigwedge_{x\in X_\sigma}f(x).
```

The quantifier is Boolean-extensional, since below $`d_{\sigma t}(f,g)`$ all corresponding values, hence their meets, agree. It belongs to the required arrow carrier. Simultaneous induction on terms proves substitution and Boolean extensionality of evaluation, admitting every allowed lambda abstraction; beta and eta hold at value 1.

The displayed equalities coincide with typed Leibniz equality. Every predicate is Boolean-extensional, giving one direction. For the reverse, the admitted predicate $`z\mapsto d_\sigma(z,x)`$ separates $`x,y`$ to precisely their equality value. The equality laws themselves follow by induction on type.

Column permutations act on base carriers through their Boolean coordinates, and on arrows by conjugation:

```math
(\pi f)(x)=\pi_\tau\bigl(f(\pi_\sigma^{-1}(x))\bigr).
```

Equality and all logical operations are equivariant. For quantifiers, the permutation is a bijection of the quantified carrier. The term induction consequently gives equivariance even for terms involving arbitrarily high quantification.

## 3. An ordinary Henkin quotient

Choose a Boolean ultrafilter $`U`$ on $`B`$ and identify $`x,y`$ when $`d_\sigma(x,y)\in U`$. Write $`L_\sigma`$ for the quotient. Application and logical constants descend to it, and $`L_t=2`$.

The necessary quantifier check is witness attainment. For an extensional Boolean predicate $`A`$, put $`b=\bigvee_x A(x)`$. Below $`b`$, choose a maximal antichain of pieces $`a_j`$, each with $`a_j\le A(x_j)`$. Add $`\neg b`$ to the partition and mix the witnesses, using a dummy object on the remaining piece. Extensionality gives $`b\le A(x)`$ for the mixed witness; the reverse inequality follows from the definition of $`b`$. Thus the join is attained.

This proves the ordinary truth lemma for the quotient. In particular, if $`\bigwedge_x A(x)\notin U`$, witness attainment for $`\neg A`$ supplies a counterexample whose Boolean truth belongs to $`U`$. Conversely, membership of the meet implies membership of every instance. Existential quantification is dual; the other cases are immediate.

Equality is therefore equality of quotient objects. If two arrow classes agree on every quotient argument, their universally quantified equality is true. Its Boolean value is their arrow equality, so the classes are equal. We can identify $`L_{\sigma\tau}`$ with a collection of actual functions from $`L_\sigma`$ to $`L_\tau`$. Lambda closure and quantification over every specified $`L_\sigma`$ are inherited. This is an extensional two-valued Henkin hierarchy, which need not contain all external functions. It meets the [generalized leaf assumptions](observer-term-closed-profile-models.md#8-henkin-leaves-and-the-exact-witness-condition).

## 4. Low-type objects are ground values on Boolean pieces

Let $`S`$ be the full ordinary two-valued hierarchy over $`\omega`$. Define

```math
\mathrm{ord}(e)=\mathrm{ord}(t)=0,\qquad
\mathrm{ord}(\sigma\tau)=\max\{\mathrm{ord}(\sigma)+1,\mathrm{ord}(\tau)\}.
```

If $`\mathrm{ord}(\sigma)\le n`$, then $`|S_\sigma|\le\beth_n`$. Structural induction proves this bound: at an arrow of order $`k\ge1`$, use

```math
|S_{\alpha\beta}|\le(\beth_k)^{\beth_{k-1}}=\beth_k.
```

Put $`\rho_0=e`$, $`\rho_{j+1}=\rho_jt`$ and $`\nu=\rho_{n+1}`$. Thus $`|S_{\rho_n}|=\mu`$ and $`|S_\nu|=2^\mu\ge\kappa`$. Fix an injection $`j:\kappa\to S_\nu`$.

**Ground-value lemma.** At every type of order at most $`n`$, and also at $`\nu`$, there are representatives $`\check a`$ of the ground objects satisfying

```math
\bigvee_{a\in S_\sigma}d_\sigma(x,\check a)=1.
```

Distinct ground representatives have equality value 0, and column permutations fix each representative up to equality value 1.

At $`e`$ the assertion is the partition definition, and at $`t`$ the two pieces are $`b`$ and $`\neg b`$. At an arrow, assuming the assertions for its subtypes, extend a ground map $`f`$ by mixing $`\check{f(a)}`$ on the disjoint pieces $`d_\sigma(x,\check a)`$. This gives a Boolean-extensional representative $`\check f`$.

For a general $`g`$, each $`g(\check a)`$ is ground-valued on a Boolean partition. When $`|S_\sigma|<\kappa`$, the distributivity lemma simultaneously refines these partitions for all ground inputs. On each resulting piece, the outputs define a ground function table. Since every input is ground-valued on pieces, extensionality makes $`g`$ agree there with that table on all inputs. The refinements cover 1, proving the displayed equality.

Every low arrow has input cardinality below $`\kappa`$, so structural induction applies. The extra type $`\nu`$ also qualifies because its input has size $`\mu<\kappa`$, even though $`S_\nu`$ may be larger. A differing ground input proves disjointness of different ground maps. Uniqueness of each mixture up to equality value 1 proves permutation invariance of the representatives.

This lemma does not identify the quotient low domains with $`S`$: an arbitrary ultrafilter need not choose a member of an infinite partition. The proof below uses equality on Boolean pieces, not such an identification.

## 5. A nonempty family with no term-selected member

Set $`\sigma=\nu t`$. Define

```math
c_i(x)=\bigvee_{\alpha<\kappa}
\bigl(d_\nu(x,\check{j(\alpha)})\wedge b_{i,\alpha}\bigr),
\qquad
F(x)=\bigvee_{i<\kappa}d_\sigma(x,c_i).
```

Both definitions are Boolean-extensional, so $`c_i\in X_\sigma`$ and $`F\in X_{\sigma t}`$. We have $`F(c_i)=1`$. For $`i\ne k`$, $`d_\sigma(c_i,c_k)=0`$: below any basic condition, a fresh coordinate allows opposite bits in the two columns, yielding unequal values at the corresponding ground input. Column permutations permute the $`c_i`$ and fix $`F`$.

**Nonselection lemma.** If $`u(F,z_1,\ldots,z_m)`$ is a finite term of type $`\sigma`$ and each $`z_j`$ has order at most $`n`$, then

```math
F\bigl(u(F,z_1,\ldots,z_m)\bigr)=0.
```

Suppose otherwise. Some index $`i`$ has a nonzero equality value between the term and $`c_i`$. Refine this positive Boolean piece so that all finitely many low parameters equal ground representatives, and take a basic condition $`p`$ below it. Substitution gives

```math
p\le d_\sigma(v,c_i),\qquad
v=u(F,\check a_1,\ldots,\check a_m).
```

Choose a column $`k\ne i`$ outside the support of $`p`$, and transpose $`i,k`$. Equivariance fixes $`v`$ up to equality value 1, so $`\pi p\le d_\sigma(v,c_k)`$. But $`p`$ and $`\pi p`$ are compatible: at the exchanged columns only one contributes entries, and elsewhere they agree. Their common extension would lie below $`d_\sigma(c_i,c_k)=0`$, a contradiction. There is no restriction on intermediate types or quantifiers in the term.

In the quotient $`L`$, let $`N`$ be the closure under all finite typed terms of $`[F]`$ together with every object at every type of order at most $`n`$. Substitution proves term closure. Every finite tuple of generators has representatives to which the lemma applies. Consequently

```math
N_\tau=L_\tau\quad(\mathrm{ord}(\tau)\le n),\qquad
[F]\in N_{\sigma t},\qquad
[F]\text{ is nonempty in }L\text{ but has no member in }N_\sigma.
```

## 6. The comparison and the theorem

Apply the coherent-profile construction to $`(L,N)`$ and $`(L,L)`$. Both models satisfy C. The first fails BF at $`\sigma`$, witnessed by the profile with constant-Top current function and future function $`\neg[F]`$. It also fails Functionality and relational OS. In the second, every transport is onto; identity and the terminal reader provide full OS.

Their reducts through order $`n`$ agree. The bases agree. At a low arrow, the input and output domains agree by induction, and the permitted future functions agree because $`N_\tau=L_\tau`$ at that arrow type. Hence the sets of coherent profiles and the operations agree. Every sentence whose elaborated types have order at most $`n`$ therefore has the same truth in both models.

A finite proposed equivalent axiom set has such a bound, so it cannot distinguish the models. The same argument handles an infinite axiom set with a uniform finite bound. Count every logical-operator and lambda-subterm type: $`Q_\tau`$ has order $`\mathrm{ord}(\tau)+2`$.

Since the first model fails BF while the second satisfies OS, the conclusion holds for every intermediate theory from C + BF to C + OS, including full Functionality and Tractarianism through their established equivalence with BF. It concerns fixed-type axioms. An externally varying type schema, or a finite strictly stronger theory, is compatible with the theorem.

## Sources

Typed construction and application: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), original direct proof §§2–7 and witness analysis §§1–3, unpaginated; exact source versions are in the [manifest](../evidence/source-manifest.json). The original forcing proof supplies an independent route using the same column symmetry.

For the general fullness and ultrafilter-quotient theorem, see Joel David Hamkins, [*A gentle introduction to Boolean-valued model theory*](https://jdh.hamkins.org/a-gentle-introduction-to-boolean-valued-model-theory/), 4 April 2021, the definition of fullness and “Boolean ultrapowers,” unpaginated. The mixing argument above verifies witness attainment for this particular typed hierarchy; the OS construction is not attributed to that reference.
