# Direct group models for reversible separation

Every C + Rev model has a direct representation by sets and ordinary Henkin functions indexed by a group. Its typed domains are preserved up to isomorphism. Group models are sound and strongly complete for C + Rev; in a countable language one fixed countable free group suffices for completeness.

## 1. The models

Work in ZFC with the fixed relational types. Choose a group $`G`$ with identity $`1`$, a nonempty individual domain $`D_e`$, and a Boolean subalgebra $`B\subseteq\mathcal P(G)`$. Put $`D_t=B`$ and take nonempty ordinary function domains $`D_{\sigma\tau}\subseteq D_\tau^{D_\sigma}`$. Require parameterized lambda closure and admission of the logical operations, including

```math
Q_\sigma(F)=\bigcap_{a\in D_\sigma}F(a),
\qquad
R_g(A)=\{h\in G:hg\in A\}\quad(g\in G)
```

Every displayed quantifier intersection must belong to $`B`$, and each $`Q_\sigma`$ and $`R_g`$ must belong to its operation domain. Admitted predicates must distinguish different individuals at $`1`$. Truth is membership of $`1`$. Define equality and native necessity by

```math
\delta_\sigma(a,b)=
\bigcap_{P\in D_{\sigma t}}(P(a)\leftrightarrow P(b)),
\qquad
\Box A=\delta_t(A,G)
```

The equality intersection is admitted by abstraction and $`Q_{\sigma t}`$. The domains need not contain every external function; intersections are required only for admitted predicates.

## 2. Inverses make equality crisp at every index

For every type,

```math
\delta_\sigma(a,b)=
\begin{cases}G&a=b,\\ \varnothing&a\ne b\end{cases}
```

Equal arguments agree under every predicate. If individuals $`a,b`$ differ, choose a predicate $`P`$ distinguishing them at $`1`$. At any $`h\in G`$, the admitted predicate $`x\mapsto R_{h^{-1}}(P(x))`$ distinguishes them. If propositions $`A,B`$ differ at $`d`$, the predicate $`R_{h^{-1}d}`$ distinguishes them at $`h`$. Unequal functions differ at an argument; an inductively available predicate distinguishing their outputs gives a predicate on the functions by abstraction. This proves the assertion at all types.

Consequently $`\Box A=G`$ exactly when $`A=G`$, and otherwise $`\Box A=\varnothing`$. The indices therefore give a constant-domain S5 interpretation of the original necessity operation.

Equivalently, one may stipulate crisp equality, require its admission and lambda closure, and omit the individual-separation clause: admitted haecceities supply that clause, and the Leibniz intersection recovers crisp equality.

## 3. Soundness

Boolean operations and quantifiers have pointwise classical truth conditions at every index. Crisp equality, function evaluation and abstraction validate substitution and beta/eta conversion. Every H theorem has value $`G`$ under every assignment.

If H proves $`A\leftrightarrow B`$, their values coincide under every assignment, so their abstractions are identical functions. This verifies C's original Logical Equivalence schema.

Inverse images preserve Boolean operations and all the required intersections:

```math
R_g(Q_\sigma(F))=Q_\sigma(\lambda a\, .\,R_g(F(a)))
```

These are identities of whole operations because the domains consist of actual functions. Moreover,

```math
R_g\circ R_k=R_{gk},
\qquad R_1=I,
\qquad R_g^{-1}=R_{g^{-1}}
```

Both inverse operations are admitted. Thus each shift is reversibly qualified at every type. If $`A\ne B`$, choose $`g`$ in their symmetric difference: $`R_g(A)`$ and $`R_g(B)`$ differ in truth at $`1`$. For different relations, choose an argument tuple giving different propositional outputs. This proves every Rev instance. At an arbitrary index $`h`$, replace the separator by $`R_{h^{-1}g}`$; the same proof gives Rev there, and hence ☐Rev.

## 4. Every Rev model has this representation directly

Start with a general Henkin model of C + Rev. The [Rev bootstrap](reversible-separation-single-sentence.md) supplies C5 and BF. The established BF/Functionality/Tractarianism equivalence represents every operation by its current function and every quantifier by the Boolean infimum of its admitted range. Write $`B`$ for the proposition algebra and $`U`$ for its currently true elements.

Let $`G`$ consist of the admitted meet-preserving operations with an admitted two-sided inverse:

```math
(\lambda p,q\, .\,E(p\land q))=(\lambda p,q\, .\,Ep\land Eq),
\qquad
\exists F^{tt}\, .\,E\circ F=I=F\circ E
```

An invertible meet homomorphism is an order isomorphism. Monotonicity follows from meet preservation; reflection follows from injectivity. Surjectivity and the order characterizations then give preservation of Top, Bottom, joins and complements.

Every such operation preserves every admitted quantifier. Put $`m=Q_\sigma(F)`$ and $`n=Q_\sigma(E\circ F)`$. Order preservation gives $`E(m)\le n`$. Choose $`b`$ with $`E(b)=n`$. Then $`E(b)\le E(F(a))`$ for every $`a`$, so $`b\le F(a)`$ for every $`a`$. The infimum property gives $`b\le m`$, hence $`n\le E(m)`$. Functionality upgrades these equalities at every input to identities of whole operations. The admitted inverse has the same properties.

Thus every member of $`G`$ and its inverse qualify at every type simultaneously. Identity, composition and inverses belong to $`G`$, which is a group under composition. Rev supplies separating members of this very group; no additional witnesses or elementary extension are needed.

Define

```math
\phi(b)=\{g\in G:g(b)\in U\}
```

Boolean preservation makes $`\phi`$ a Boolean homomorphism; Rev makes it injective. Quantifier preservation and the ordinary current truth clause give

```math
g(Q_\sigma(F))\in U
\quad\Longleftrightarrow\quad
\forall a\in D_\sigma\, .\,g(F(a))\in U
```

Therefore

```math
\phi(Q_\sigma(F))=\bigcap_a\phi(F(a)),
\qquad
\phi(g(b))=R_g(\phi(b))
```

Membership of $`1`$ preserves current truth. At $`e`$ use the identity map, at $`t`$ use $`\phi`$, and recursively transport each function $`f`$ to $`j_\tau\circ f\circ j_\sigma^{-1}`$. These are bijections onto the new typed domains. They preserve application, abstraction and logical operations; haecceities provide individual separation. Equality is preserved by its Leibniz definition. This gives the required isomorphism without enlarging a typed domain.

## 5. Strong completeness and a fixed free group

General Henkin completeness supplies a C + Rev model of $`\Gamma\cup\{\neg A\}`$ whenever $`\Gamma`$ does not prove $`A`$. Apply the direct representation:

```math
\Gamma\vdash_{\mathrm C+\mathrm{Rev}}A
\quad\Longleftrightarrow\quad
\text{every group model satisfying }\Gamma\text{ satisfies }A
```

In a countable language, choose the original model countable. Its admitted group is countable. Enumerate it and obtain a surjective homomorphism $`\pi:F_\omega\to G`$ from the free group on countably many generators. Replace each proposition $`A`$ by $`\pi^{-1}(A)`$ and transport the higher domains. Surjectivity makes this injective on propositions; inverse images preserve intersections and Boolean operations, while

```math
R_w(\pi^{-1}(A))=\pi^{-1}(R_{\pi(w)}(A))
```

All shifts remain admitted. Every countable original model has this presentation directly. An arbitrary uncountable model uses its own possibly larger group. Admission of the free generators' shifts and their inverses suffices by composition.

## 6. Higher types and pure truth

Group shifts induce coherent transports at every type:

```math
T_g^e=\mathrm{id},\qquad T_g^t=R_g,\qquad
T_g^{\sigma\tau}(f)=T_g^\tau\circ f\circ T_{g^{-1}}^\sigma
```

At relational types these operations are admitted by recursive abstraction. At $`e`$ identity is a metatheoretic map; no forbidden individual-valued operation is introduced. Type induction gives inverse transports, $`T_gT_k=T_{gk}`$, and compatibility with application.

The transports fix the logical operations. For quantifiers the calculation is

```math
R_gQ_\sigma(R_{g^{-1}}\circ F\circ T_g^\sigma)
=Q_\sigma(F\circ T_g^\sigma)=Q_\sigma(F),
```

using observer preservation and bijective reindexing. Induction on terms therefore fixes every closed pure term. A pure sentence has a shift-invariant value $`A`$, and transitivity of group translation makes $`A=G`$ or $`A=\varnothing`$. This gives a semantic proof of the established Rev ⇒ No Pure Contingency theorem. For a sentence with constants, the argument requires those constants to be fixed by the transports.

The same data give a one-object group-action presentation: the profile associated with $`f`$ is $`\alpha_f(g,a)=T_g^\tau(f(T_{g^{-1}}^\sigma(a)))`$. Admission of the proposition shifts remains an explicit requirement.

If the proposition algebra contains an atom, a shift makes it true. That true atom lies below every true proposition; shifting it back produces an atom below any nonzero proposition. Thus the algebra is either atomless or atomic with Actuality. Full powersets and full function spaces are stronger assumptions and are not needed here.

## Sources and comparison

New representation and proofs: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), §§1–6 of this presentation; source correspondence is in the [manifest](../evidence/source-manifest.json).

The [ordinary OS representation](observer-shift-semantics.md) supplies the monoid comparison. The BF equivalences are Bacon–Dorr, *Classicism*, 16 May 2023 draft, Proposition 2.1 and n. 27, pp. 20–21. General BBK completeness is Theorem 3.2 and n. 64, pp. 44–45, in the [1 July 2022 draft](https://andrew-bacon.github.io/papers/Classicism.pdf).

The [finite-block model](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/finite-block-symmetry-reversible-gap.md) already separates C5 + ☐OS from Rev. The group representation retains that distinction.
