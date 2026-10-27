# Observer propagation for CH and analysis

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source for the new combinations, finite scope audit, and countermodel verification: `misc`, this note §§1–6, unpaginated. No native records, human proofs, or formal-verification statuses are changed.

**Results.** Current universal CH and analytical truth propagate under OS + Functional Choice, and under C5 + OS + Rigid Comprehension. The latter needs only unary, binary, and ternary comprehension at the selected carrier type. Ordinary separation alone does not suffice: a relative model below has full necessary native-Box separation, necessary BF, necessary Relational Choice, and necessary propositional Boolean Completeness, yet CH and a first-order analytical sentence are currently true of every real structure and possibly false. Actual real structures exist at the same selected type, so this failure is not vacuous. That model fails C5. The C5 + OS case without additional comprehension or choice remains unresolved by this audit.

## 1. Exact claims, sources, and the nonvacuity issue

At an admitted type $`\sigma`$, put

```math
\begin{aligned}
H_\sigma&:=\exists\mathfrak R\,\mathrm{Real}_\sigma(\mathfrak R),\\
U_{\sigma,\varphi}&:=\forall\mathfrak R\,
 [\mathrm{Real}_\sigma(\mathfrak R)\to\varphi(\mathfrak R)]
\end{aligned}
\tag{1}
```

The propagation question is $`U_{\sigma,\varphi}\to\Box U_{\sigma,\varphi}`$. For CH, $`\varphi=\mathrm{CH}`$. For first-order analysis, $`\varphi`$ is any sentence in the ordered-field relational language **including the natural-numbers predicate**.

These are not the already-modal principles

```math
\Box U_{\sigma,\varphi}\ \lor\ \Box U_{\sigma,\neg\varphi}
\tag{2}
```

The fresh upstream snapshot `a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb`, parsed selectively from `/tmp/classicism-upstream-a89a5058-decoded.json`, records (2) as Necessity of Analysis for first-order analytical sentences, and as Non-contingency of CH for CH. The native checkout is older. The Background's Analysis section, also available in the retained upstream source copy, specifies

```math
\mathfrak R=(X^{\sigma t},\le^{\sigma\sigma t},
+^{\sigma\sigma\sigma t},\times^{\sigma\sigma\sigma t},
0^\sigma,1^\sigma,N^{\sigma t})
```

Completeness concerns nonempty bounded admitted subproperties. $`N`$ is the least admitted inductive subproperty of $`X`$. CH says that every admitted subproperty of $`X`$ injects into $`N`$ or is in bijection with $`X`$, with injections and bijections represented by binary relations. Neither an individual-valued operation nor an external full powerset is part of this definition.

There is a useful logical qualification. Formula (2), current $`U_{\sigma,\varphi}`$, and actual $`H_\sigma`$ imply $`\Box U_{\sigma,\varphi}`$: the opposite boxed disjunct contradicts current truth in an actual real structure. Without actual existence, that elimination is unavailable. Analytic Necessitism supplies the missing existence whenever $`H_\sigma`$ is possible; if it is impossible, $`\Box U_{\sigma,\varphi}`$ holds vacuously. Thus Analytic Necessitism plus its recorded invariance theorem gives the propagation implication even without a separate actual-existence premise. Second-Order Analytic Necessitism does the same for CH and other finite second-order analytical sentences.

## 2. Positive propagation and its finite comprehension scope

The established observer results give

```math
\begin{aligned}
\mathrm C+\mathrm{OS}+\mathrm{FC}_{\rm all}
&\Rightarrow\Box\mathrm{FC}_{\rm all},\\
\mathrm{C5}+\mathrm{OS}+\mathrm{RigidComp}_{\rm all}
&\Rightarrow\Box\mathrm{RigidComp}_{\rm all}
\end{aligned}
\tag{3}
```

See [Choice audit](../../../next-update/proofs/observer-choice-transport.md), §2, and [Rigidity audit](../../../next-update/proofs/observer-comprehension-reflection.md), §§2–4. No optional premise is necessitated. The fresh snapshot's proved records then give

```math
\Box\mathrm{FC}\Rightarrow\Box\mathrm{Plenitude}
\Rightarrow\mathrm{C5}+\mathrm{Atomicity}
\Rightarrow\mathrm{C5}+\Box\mathrm{RigidComp}
\Rightarrow\mathrm{SecondOrderAnalyticNecessitism}
\tag{4}
```

The same final necessitism follows directly from the second package in (3). Its recorded consequences include Analytic Necessitism, Necessity of Analysis, Necessity of Second-Order Analysis, and Non-contingency of CH. With §1's existence argument, both packages therefore imply

```math
U_{\sigma,\varphi}\to\Box U_{\sigma,\varphi}
\tag{5}
```

for every first-order or finite second-order analytical sentence, in particular CH. The corresponding statement for $`\neg\varphi`$ holds too. These are consequences of the stronger structural results, not an independent discovery that those already-modal principles are necessary.

**Finite local refinement for CH and first-order analysis.** Fix $`\sigma`$, write $`\rho_k=\sigma^kt`$ for the curried $`k`$-ary relation type, and take

```math
\Delta=\{\sigma,\rho_1,\rho_2,\rho_3\}
```

It suffices to assume C5, the single ordinary propositional separation instance $`S_{t,\Delta}`$, and current Rigid Comprehension at $`\rho_1,\rho_2,\rho_3`$. The local rigidity-reflection theorem boxes exactly these three instances. The ordinary proof of the upstream result `c5-and-necessary-rigid-comprehension-imply-second-order-analytic-necessitism` uses them as follows:

- Unary comprehension rigidifies $`X,N`$ and each subproperty used in completeness and leastness.
- Binary comprehension rigidifies the order; ternary comprehension rigidifies the two field-operation graphs.
- The represented power of arity $`k`$ is defined directly as the property of rigid $`k`$-ary relations supported on the rigid carrier. Its rigidity follows from C5 and BF; no comprehension at $`(\rho_k)t`$ is used. Representation of an arbitrary relation uses comprehension only at $`\rho_k`$, applied to its restriction to the carrier.

Consequently the three boxed instances give a necessarily real rigid structure whenever one is possible, and represented powers of arities one and two. These suffice for CH; first-order analytical sentences need only the rigid structure. They give (5) at this $`\sigma`$.

The [analytic rigidification proof](../../../classicism-results-2026-10-24-v2/proofs/analytic-rigidification.md), “Internal transport argument” and “Represented powers”, supplies these uses. All-type C5 remains a premise of this finite refinement.

The native-record portions of (4) and the consequences of C5 + necessary Rigid Comprehension were checked using a proved-only Engine on the fresh snapshot, with empty background and the optional assumptions in the queried premise sets.

## 3. Metatheory and an extensional leaf with opposite mathematics

For the counterexample assume explicitly an ambient universe

```math
V\models\mathrm{ZFC}+V=L
```

containing a countable model $`M\models\mathrm{ZFC}+\neg\mathrm{CH}`$. This is the exact metatheoretic assumption of the construction. No claim that ZFC proves the existence of such a model is made. **M need not be transitive or externally well founded.** All references to its real numbers, powersets, and functions below mean its internal objects, externally interpreted through its membership relation.

Construct a one-world extensional Henkin typed structure $`H`$ by carrying out the full relational type hierarchy internally in $`M`$:

```math
D_e(H)=\mathbb R^M,\qquad D_t(H)=\{0,1\},
```

and, for each admitted arrow type, use the functions that $`M`$ says belong to the corresponding function set. Externalize each internal set as its set of members in the countable structure $`M`$, and use $`M`$'s application relation. Internal extensionality ensures that distinct internal functions have distinct applications at some internal argument, so this gives an ordinary external Henkin structure with literal function application.

Every fixed finite typed formula translates to a first-order set-theoretic formula evaluated in $`M`$. The internal full powersets/function spaces and Separation give the required lambda closure. Ordinary identity and two-valued extensional truth give H, Extensionality, and hence C at this leaf. Native Box is truth itself. Identity is a logical observer at every finite qualification list and separates at every relational type. Internal Choice in $`M`$ gives both choice schemas, including Relational Choice with individual outputs. These statements do not require external full powersets of the countable domains.

Let $`\sigma=et`$. Internally in $`M`$, the injection

```math
x\longmapsto\{x\}:\mathbb R^M\longrightarrow
\mathcal P^M(\mathbb R^M)
\tag{6}
```

puts a copy of its complete ordered real field, with its natural-numbers predicate, on a subproperty of the $`et`$-domain. All required field relations are internal relations and therefore admitted. Completeness is exactly completeness for $`M`$'s admitted subproperties. Thus $`H`$ has a real structure at $`et`$, and $`U_{et,\mathrm{CH}}`$ is false there because $`M\models\neg\mathrm{CH}`$.

For first-order analysis use the finite parameter-free analytical sentence $`\varphi_L`$ expressing “every real is constructible”. Its translation into the required field language with $`N`$ is given in [Analytical sentence audit](../dependencies/analytical-sentence.txt). The coding equivalence is a theorem interpreted internally in $`M`$; nonstandard natural numbers in $`M`$ cause no substitution of external semantics. ZFC proves that if every real is constructible then CH: the constructible well-order of the constructible reals has length $`\omega_1^L\le\omega_1`$, and Cantor's theorem gives the reverse cardinal bound. Hence $`M\models\neg\varphi_L`$, and the real structure just constructed falsifies $`\varphi_L`$. Therefore $`U_{et,\varphi_L}`$ is false at $`H`$ too.

## 4. An unrestricted predecessor with logical observers

Adjoin one root $`r`$ with one arrow to $`H`$, using the standard unrestricted coalesced-root construction. Give it

```math
D_e(r)=D_e(H),\qquad
D_{\bar\sigma t}(r)=
\mathcal P^V\!\left(\prod_jD_{\sigma_j}(r)\right)
\times D_{\bar\sigma t}(H)
\tag{7}
```

For the empty tuple this gives $`D_t(r)=2\times2`$. A root relation consists of an arbitrary actual extension and a leaf relation. Its transport is the second projection. Every projection is onto: pair a leaf relation with the empty current extension. The individual projection is identity.

Application uses the current row and the leaf application; lambda terms use their current extension and their leaf interpretation. Onto projections make the leaf coordinate of a root quantifier agree with the leaf quantifier. Arbitrary current rows supply the actual truth clauses and distinguish unequal root entities; at the leaf, identity is literal identity of the projected entities. These facts validate the standard coalesced C semantics. In particular an unconditional H-equivalence holds in the actual rows and at the leaf, and hence identifies the two abstractions. No optional equivalence is passed to C's theoremhood rule.

Write a root proposition as $`(\epsilon,b)`$, with actual truth $`\epsilon`$. Besides identity, admit the reader

```math
E_\ell(\epsilon,b)=(b,b)
\tag{8}
```

It is the root $`tt`$-entity whose actual extension reads the second bit and whose leaf operation is identity. It preserves the Boolean operations. At every type, its actual quantifier identity compares quantification over projected root arguments with quantification over leaf arguments; the projections are onto, so both universal and existential identities hold. At the leaf its transported operation is identity. Thus the laws hold for all future inputs and are whole-operation identities, at every finite requested qualification list.

Identity distinguishes unequal first bits, and $`E_\ell`$ distinguishes unequal second bits. For higher relations, different current rows differ at a current tuple. Different leaf relations differ at a leaf tuple by leaf extensionality; lift that tuple through the onto projections and apply $`E_\ell`$. Hence root OS holds at every relational output type and finite list. Leaf OS is already true, so its separately boxed schema holds at the root as well.

This reader also preserves native Box. Directly from the defined identity,

```math
\Box(\epsilon,b)=(\epsilon\land b,b),
```

and therefore

```math
E_\ell(\Box p)=\Box(E_\ell p)=(b,b)
\tag{9}
```

Identity has this property too, and the leaf observers are identity. Thus the same separation proof gives **full BoxSep and its separately boxed schema**.

The following additional flags have direct checks:

- BF holds at the root because projections are onto, and at the leaf because Box is truth. Hence boxed BF holds at every type.
- Relational Choice holds currently by external Choice in $`V`$: represent an actual selector graph as the current row in (7), using any leaf relation. It holds at the leaf by internal Choice in $`M`$. Hence boxed Relational Choice holds.
- Propositional Boolean Completeness holds at both evaluations: their proposition algebras are respectively the finite algebras $`2\times2`$ and $`2`$. Thus boxed BC at $`t`$ holds.

C5 fails. The root-only proposition $`q=(1,0)`$ is currently distinct from Bottom, but both transport to the leaf's false proposition. Thus its distinctness from Bottom is not necessary. No C5 counterexample is claimed.

This construction is the one-leaf specialization of the unrestricted coalesced-root method in [Complete Boolean root](../complete-boolean-root.md), §§3 and 5, with an extensional Henkin leaf. It uses an admitted reader of an actual two-valued leaf. It does **not** use an arbitrary ultrafilter on a full atomless Boolean-valued model as a quantifier-preserving observer.

## 5. Nonvacuous current CH and analytical truth at the root

Every leaf domain is a subset of the countable model $`M`$. In particular $`D_e(r)=\mathbb R^M`$ is externally countably infinite. Therefore

```math
D_{et}(r)=\mathcal P^V(D_e(r))\times D_{et}(H)
```

has cardinality equal to the ambient continuum. Put an ordinary complete ordered real field of $`V`$ on this carrier, with the ordinary $`N`$. The actual rows in (7) admit its domain, order, field graphs, and $`N`$, paired with arbitrary compatible-type leaf components. They also admit every external subproperty of this carrier. Hence it is an actual real structure in exactly the native definition. In particular,

```math
r\models H_{et}
\tag{10}
```

Conversely, every root real structure at $`et`$ is complete with respect to **all ambient subsets** of its carrier, because every such subset is an actual row of an admitted predicate. Thus the usual categoricity of complete ordered fields identifies it with $`\mathbb R^V`$; its least inductive predicate is the usual natural-number predicate. The same actual fullness covers the binary relations used to express CH. Since $`V=L`$, all such structures satisfy both CH and $`\varphi_L`$.

At the leaf, §3 gave real structures at the same type $`et`$ falsifying both sentences. Consequently the root satisfies simultaneously

```math
\boxed{
\begin{gathered}
\mathrm C+\Box\mathrm{BoxSep}
+\Box\mathrm{BF}_{\rm all}
+\Box\mathrm{RelChoice}_{\rm all}
+\Box\mathrm{BC}_{t},\\
H_{et}\land U_{et,\mathrm{CH}}\land U_{et,\varphi_L},\\
\Diamond\neg U_{et,\mathrm{CH}}
\land\Diamond\neg U_{et,\varphi_L}
\end{gathered}}
\tag{11}
```

The two universal truth propositions in (11) each have value $`(1,0)`$. Their boxes are false. Their universal negations are false at the root because real structures actually exist, so neither corresponding modal disjunction (2) holds. The model therefore also refutes Non-contingency of CH and Necessity of Analysis.

These are genuine current-to-possible-failure examples at a type with actual real structures. They remain bare-C examples: §4's explicit distinctness collapse prevents adding C5.

The [finite-support symmetric model](necessary-os-ch-inaccessible-countermodel.md) supplies the distinct C5 + ☐OS CH countermodel under a strongly inaccessible cardinal. The [two-Hechler construction](necessary-os-analysis-countermodel.md) gives analytical contingency under C5 + ☐OS.
