# Generic evaluation of a Boolean model: independent observer and forcing audit

25 October 2026. Ordinary mathematical audit by OpenAI Codex. Direct source for the connecting argument: `misc`, this note, §§1–7, unpaginated. No Lean certification, database edit, or claim of historical novelty.

**Verdict.** The construction below gives, relative to $`\mathrm{Con}(\mathrm{ZFC})`$, countermodels to propagation of CH and analytical truth under **C5 + SplitMono**, hence also under **C5 + BoxSep** and **C5 + ordinary OS**. The CH variant has current $`U_{t,\mathrm{CH}}`$ and false $`\Box U_{t,\mathrm{CH}}`$. The analytical variant has current $`U_{t,\neg\varphi_L}`$ and false $`\Box U_{t,\neg\varphi_L}`$, where $`\varphi_L`$ is the fixed first-order analytical sentence expressing that every real is constructible. Both variants have real structures with Boolean value Top, so these failures are nonvacuous. The observer hypotheses hold currently, not necessarily.

## 1. Internal Boolean model and external generic evaluation

Let $`M`$ be a countable model of ZFC, not assumed transitive or well founded. All constructions described as internal below take place in $`M`$. Let $`A`$ be an internally complete atomless Boolean algebra, and put

```math
B=2\times A,\qquad a=(1,0),\qquad b=(0,1)
```

Use the internal full function hierarchy at precisely the admitted relational types:

```math
D_e=E\ne\varnothing,\quad D_t=B,\quad
 D_{\sigma\rho}=(D_\rho^{D_\sigma})^M\quad(\rho\ne e)
```

Externalize each internal set and its application operation. Internal extensionality makes these honest, possibly non-full, external function domains: distinct represented functions differ on some represented argument. Identity is crisp literal identity at every type. Connectives are the internal Boolean operations; quantifiers are the internally computed meets and joins.

There are only countably many dense subsets of $`A^+`$ represented in $`M`$. Construct an external ultrafilter $`G`$ meeting all of them, and designate

```math
v_G(\varepsilon,d)=1\quad\Longleftrightarrow\quad d\in G
 \tag{1}
```

No assertion that $`G`$ belongs to $`M`$, or is complete for arbitrary external families, is used.

The crucial quantifier check is exact. For every $`M`$-coded family $`(d_i)_{i\in I}`$, let $`s=\bigvee^M_i d_i`$. The internally coded set

```math
\{c>0:c\le\neg s\ \text{or}\ (\exists i\in I)\ c\le d_i\}
```

is dense. Meeting it proves

```math
\bigvee\nolimits_i^M d_i\in G
 \quad\Longleftrightarrow\quad
 (\exists i\in I^M)\ d_i\in G                       \tag{2}
```

The universal version follows by complementation. Every standard finite typed formula, including its instances with admitted parameters, produces an $`M`$-coded family. Thus (1) gives ordinary external quantifiers over the externalized typed domains. Internal satisfaction of bounded assertions about these sets is precisely external satisfaction over their represented members; nontransitivity causes no extra assumption here.

The internal Boolean verification of H and theoremhood-restricted Logical Equivalence now externalizes to a model of C. In particular, lambda closure is internal Separation/function formation, and H-equivalent bodies have identical represented functions. Since identity is crisp,

```math
\llbracket\Box P\rrbracket=
 \begin{cases}1_B&\llbracket P\rrbracket=1_B,\\0_B&\text{otherwise.}\end{cases} \tag{3}
```

This gives C5. The same computation gives boxed BF at every type: an internal meet is Top exactly when all its entries are Top. This is a Boolean-value computation, not necessitation of an optional premise.

## 2. Ordinary separation from weak homogeneity

Assume $`M`$ regards $`A`$ as weakly homogeneous: for all $`d,c>0`$, some internal automorphism $`\alpha`$ has $`c\wedge\alpha(d)>0`$. Then for each $`d>0`$,

```math
D_d=\{c>0:(\exists\alpha\in\mathrm{Aut}(A)^M)\ c\le\alpha(d)\}
```

is internally dense. Genericity supplies an internal $`\alpha`$ with $`\alpha(d)\in G`$.

The admitted maps

```math
E_\alpha(\varepsilon,d)=(\varepsilon,\alpha(d)),
 \qquad E_0(\varepsilon,d)=(\varepsilon,\varepsilon1_A)
 \tag{4}
```

are internal complete Boolean homomorphisms. Consequently they preserve all internally indexed meets and joins. In the full internal hierarchy these are the **whole-operation** quantifier identities of $`\mathrm{Good}_\Delta`$, for every finite external list $`\Delta`$; crisp equality supplies the equality clauses. Their qualification is never inferred merely from preservation of currently true instances.

If two propositions have different first bits, $`E_0`$ separates their truth values at $`G`$. Otherwise their tail symmetric difference $`d`$ is nonzero; choose $`\alpha`$ with $`\alpha(d)\in G`$, and $`E_\alpha`$ separates them. Distinct higher relations differ on an admitted finite argument tuple, so this proves full typed OS.

## 3. Qualified left inverses and native Box

For the forcings in §5, every nonzero basic condition $`c`$ has an internal complete Boolean isomorphism

```math
h:A\longrightarrow A\mathbin{\upharpoonright}c
```

Choose such a proper $`c\notin G`$, for example one of two incompatible nonzero basic conditions. Define

```math
E(\varepsilon,d)=(\varepsilon,\varepsilon\neg c\vee h(d)),
 \qquad
 F(\varepsilon,d)=(\varepsilon,h^{-1}(d\wedge c))
 \tag{5}
```

Both are admitted internal complete Boolean homomorphisms. For $`E`$, the tail is the product decomposition into the $`\neg c`$ and $`c`$ pieces; for $`F`$, projection onto the $`c`$ piece followed by $`h^{-1}`$ preserves the internal Boolean operations and arbitrary internal joins/meets. Direct calculation gives the whole identity $`F\circ E=I`$. At $`G`$, $`E`$ reads the first bit, since $`h(d)\le c\notin G`$ and $`\neg c\in G`$.

Replace $`E_0`$ in §2 by this $`E`$. The maps $`E_\alpha`$ have admitted qualified two-sided inverses $`E_{\alpha^{-1}}`$. Thus all the separating witnesses have qualified left inverses: full **SplitMono** holds. Each separating observer is injective and fixes Top, so

```math
E(d)=1_B\iff d=1_B
```

Equation (3) gives the whole native-Box commutation identity. Hence full **BoxSep** holds as well.

## 4. Transfer of CH and analytical truth

Use the [extensional forcing transfer lemma](../dependencies/c5-functional-choice-analysis.md), §§2–4. It applies internally in $`M`$, then externalizes by §1. Its scope is finite, box-free extensional structure formulas, with carrier equality and relation variables used only by application. It does not identify higher-type intensional identity with equality of extensions.

For $`S=D_t=B`$, the required capacity conditions are

```math
M\models|\mathbb R|\le|B|,
 \qquad M\models 1_A\Vdash|\mathbb R|\le|\check B|
 \tag{6}
```

They give a mixed real structure $`\mathfrak R_*`$ with $`\llbracket\mathrm{Real}_t(\mathfrak R_*)\rrbracket=1_B`$, and, for the universal structural sentence,

```math
\llbracket U_{t,\varphi}\rrbracket
 =\bigl(\mathbf1_{M\models\varphi(\mathbb R)},
          \|\varphi(\mathbb R)\|_A^M\bigr)           \tag{7}
```

Here $`U_{t,\varphi}=\forall\mathfrak R(\mathrm{Real}_t(\mathfrak R)\to\varphi(\mathfrak R))`$. Real completeness is for **nonempty bounded** subproperties, and the natural-numbers predicate is included. The same lemma covers CH's extensional second-order formula. Its proof uses all internally admitted subset names, not only ground extensions. Equation (7) is an internally proved finite mathematical assertion; it therefore remains applicable when $`M`$ is nonstandard.

## 5. Two forcing choices, including literal CH propagation

**Cohen variant.** Take $`M\models V=L`$ and $`A=\mathrm{RO}(\mathrm{Add}(\omega,\omega_2))^M`$. Conditions are finite partial binary functions on $`\omega_2\times\omega`$. Moving a finite domain away from another proves weak homogeneity; a fresh coordinate gives atomlessness. Below a basic condition, deleting its assigned coordinates and reindexing the remainder identifies its cone with the original forcing. This proves the relative-algebra isomorphism needed in §3.

Internally, GCH and the usual ccc/nice-name count give $`1_A\Vdash 2^\omega=\omega_2`$, while $`|A|\ge\omega_2`$ follows from distinct coordinate generators. Thus (6) holds both for ground and forced reals. The exact values are

```math
\llbracket U_{t,\mathrm{CH}}\rrbracket=a,\qquad
 \llbracket U_{t,\neg\mathrm{CH}}\rrbracket=b
```

For the fixed first-order analytical sentence $`\varphi_L`$ from the analysis note §4, the ground satisfies $`\varphi_L`$, while Cohen forcing adds a nonconstructible real and preserves the constructible hierarchy. Hence

```math
\llbracket U_{t,\varphi_L}\rrbracket=a,\qquad
 \llbracket U_{t,\neg\varphi_L}\rrbracket=b
```

At (1), each displayed $`b`$-valued current sentence is true and its box is false. Both Non-contingency of CH and Necessity of Analysis fail. This variant alone does **not** refute the literal implication $`U_{t,\mathrm{CH}}\to\Box U_{t,\mathrm{CH}}`$, because its antecedent is currently false.

**CH-restoring collapse.** Take $`M\models\neg\mathrm{CH}`$, put $`\kappa=(2^\omega)^M`$, and let $`P`$ consist of countable partial functions from $`\omega_1`$ to $`\kappa`$, ordered by extension. Take $`A=\mathrm{RO}(P)^M`$. Internally, a countable descending sequence has its union as a condition; this gives countable closure, no new reals, and preservation of $`\omega_1`$. The generic union is total and onto $`\kappa`$, since including each coordinate and including each desired value are dense requirements. It therefore forces CH. This is the usual $`\mathrm{Col}(\omega_1,\kappa)`$; see [Karagila, Forcing lecture notes, §4.1, Definition 4.11 and Exercise 4.13, printed p. 22](https://karagila.org/files/Forcing-2023.pdf).

Permutations of the **domain** $`\omega_1`$ can move any countable support disjoint from another, proving weak homogeneity. Deleting a basic condition's countable domain leaves a set internally bijective with $`\omega_1`$, proving the cone self-similarity required in §3. A fresh coordinate with two values proves atomlessness. The $`\kappa`$-sized antichain of assignments at one fixed coordinate proves $`|A|\ge\kappa`$. The ground reals inject into $`B`$, and that injection still covers all reals after this forcing because there are no new reals. Thus (6) holds.

Now

```math
\llbracket U_{t,\mathrm{CH}}\rrbracket=b,\qquad
 \llbracket U_{t,\neg\mathrm{CH}}\rrbracket=a        \tag{8}
```

At (1), (8) refutes **literal current CH propagation**. Do not infer a first-order analytical change from this no-new-real variant; its role is the second-order CH target.

## 6. Choice, rigidity, and necessary-observer checks

There is no hidden Functional Choice premise. The admitted relation

```math
R(p,q)=(p\wedge(q=\top))\vee(\neg p\wedge(q=\bot))
```

is serial and functional with value Top. For every internal operation $`f:B\to B`$, its selecting value $`\bigwedge_pR(p,f(p))`$ decides every $`p`$; if nonzero it is an atom. Conversely each atom is attained. Since $`B`$'s unique atom is $`a`$, the existential selecting assertion has value $`a`$, and is false at (1). This is the witness calculation in the analysis note §7, now at a different designated point. Likewise $`X(p)=p`$ has rigid-coextension value $`a`$: persistent relations must be crisp, and a crisp coextension again decides every proposition. Thus current Rigid Comprehension fails, too.

Boxed Relational Choice does hold. Internally well order each output domain and disjointify a relation by

```math
T(x,y)=U(x,y)\wedge\neg\bigvee_{z<y}U(x,z)
```

The total weight is preserved, distinct outputs are disjoint, and $`T\le U`$. This gives Boolean value Top to every Relational Choice instance, including individual-output instances. It does not provide an admitted operation selecting a ground output simultaneously across all Boolean components.

Rev fails: every admitted reversible Boolean observer is a Boolean automorphism and fixes the unique atom $`a`$. At (1), it therefore cannot distinguish $`a`$ from Bottom. This failure agrees with the [positive Rev theorem](rev-analysis.md).

Finally, ordinary separation is not necessary. At the first-coordinate evaluation, every $`\mathrm{Good}_{\{t\}}`$ observer $`J`$ has $`\pi J=\pi`$. Indeed, its $`Q_t,P_t`$ identities imply preservation of all internal subsets of $`B`$ (use internally represented masked identity functions); $`\pi J:B\to2`$ is consequently an internal complete Boolean homomorphism. Its true-fibre meet is an atom, necessarily $`a`$, so it is the atom reader $`\pi`$. Such observers cannot separate $`b`$ from Bottom there. Thus $`S_{t,\{t\}}`$ has first coordinate false and its box is false at (1). The qualification $`\{t\}`$ matters: no analogous assertion is made here about observers qualified only for the empty type list.

## 7. Metatheory and bounded conclusion

The construction is conditional on a countable $`M`$ satisfying the indicated ZFC extension. Standard relative-consistency and completeness arguments supply such models from $`\mathrm{Con}(\mathrm{ZFC})`$: use ZFC+$`V=L`$ for Cohen and ZFC+$`\neg\mathrm{CH}`$ for the collapse. No countable **transitive** model assumption occurs. The externally generic truth lemma (2) is the step that permits the weaker, possibly nonstandard model assumption.

The verified current package is C5 + SplitMono + BoxSep + OS, with boxed BF and boxed Relational Choice. Current Functional Choice, current Rigid Comprehension, Rev, and boxed OS fail. No Boolean Completeness assertion is made at this new evaluation point. The two variants settle the weaker-observer CH/analysis question left bounded in [the earlier audit](ch-analysis-audit.md), while leaving the established affirmative Rev result intact.
