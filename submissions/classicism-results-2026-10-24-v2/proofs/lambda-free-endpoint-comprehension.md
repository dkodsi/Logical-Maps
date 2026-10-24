# Endpoint separation and Infinitary Comprehension over λ-free H

OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the reconstruction and the observer extension of the countermodel: `misc`, §§1–6, unpaginated.

**Endpoint separation + boxed Infinitary Comprehension, over the λ-free base specified below, characterizes full standard relational hierarchies in ZF.** Finite instances of the comprehension schema reconstruct abstraction. Translated equality clauses are unnecessary in the initial observer qualification: they follow in the reconstructed theory.

## 1. Base and two principles

Use the original relational types: bases $`e,t`$, with $`\sigma\rho`$ admitted only when $`\rho\ne e`$. The λ-free base has variables, application, typed equality and its substitution rules, primitive Boolean formula constructors, and object quantifier binders. There is no abstraction constructor, Comprehension, Intensionality, or independently assumed family of logical objects representing those constructors. Write $`\Box A:=(A=\top)`$. Implication and biconditional are Boolean abbreviations. The selected axiom schemas are global, with theorem necessitation; this does not enlarge C's H-theoremhood gate for Logical Equivalence.

For each finite tested-type list $`\Delta`$, call $`O^{tt}`$ qualified when it fixes $`\top`$, is endpoint-valued, and satisfies strict Boolean and quantifier preservation:

```math
\begin{gathered}
O\top=\top,\qquad \forall p\, .\,(Op=\top\lor Op=\bot),\\
\forall p\, .\,O(\neg p)=\neg Op,\\
\forall p,q\, .\,O(p\land q)=Op\land Oq,\qquad
\forall p,q\, .\,O(p\lor q)=Op\lor Oq,\\
\forall F^{\sigma t}\, .\,O(\forall x^\sigma\, .\,Fx)=\forall x^\sigma\, .\,O(Fx),\\
\forall F^{\sigma t}\, .\,O(\exists x^\sigma\, .\,Fx)=\exists x^\sigma\, .\,O(Fx)
\qquad(\sigma\in\Delta).
\end{gathered}
```

Write $`Q_\Delta(O)`$ for these conditions. Top-fixing is explicit because $`\top`$ may be primitive. The displayed equations are object identities, including the quantified equations; they are not material preservation conditions. No preservation of native necessity or infinitary connectives is imposed.

**Endpoint separation** is the full typed schema, for every relational $`\tau=\bar\sigma t`$ and finite $`\Delta`$:

```math
\forall X,Y^\tau\, .\,\left[X=Y\leftrightarrow
\forall O^{tt}\, .\,\left(Q_\Delta(O)\to
\forall\bar x\, .\,[O(X[\bar x])\leftrightarrow O(Y[\bar x])]
\right)\right].
```

The tuple may be empty. Application $`X[\bar x]`$ is explicitly left-nested. Types and finite type lists index the schema; they are not quantified objects.

**Boxed Infinitary Comprehension** says:

```math
\exists R^{\sigma_1\cdots\sigma_n t}\, .\,
\Box\forall x_1\cdots x_n\, .\,
\bigl(R[\bar x]\leftrightarrow A\bigr).
```

Here $`A`$ is a well-founded set-sized infinitary matrix with ordinary classical truth clauses, arbitrary set-sized Boolean conjunctions and disjunctions, and arbitrary simultaneous typed parameter families. Every instance holds under every such assignment. The bound argument tuple is finite, possibly empty; its types may include $`e`$. The representing variable is fresh. No fixed cardinal bound or well-orderability restriction is imposed.

## 2. K, Intensionality and Functionality from separation

First derive K. Suppose $`p=\top`$ and $`(p\to q)=\top`$. Every qualified observer fixing top accepts $`p`$ and $`p\to q`$. Boolean preservation therefore makes it accept $`q`$. It also accepts $`\top`$, so propositional separation gives $`q=\top`$. Discharging these premises yields

```math
\Box(p\to q)\to(\Box p\to\Box q).
```

The same argument with $`(p\leftrightarrow q)=\top`$ makes every qualified observer agree on $`p,q`$. Thus

```math
\Box(p\leftrightarrow q)\to p=q.
```

Necessitating pure universal instantiation and applying the derived K gives boxed universal instantiation. Consequently, from $`\Box\forall\bar x\, .\,(X[\bar x]\leftrightarrow Y[\bar x])`$, obtain equality of the proposition values at each tuple. Equality substitution makes every observer agree on those values. Full typed separation gives $`X=Y`$. This is relational Intensionality.

Full typed separation also gives Functionality directly: if two operations have identical values at every argument, their saturated proposition values have identical observer outputs, so the operations are equal. These arguments use no abstraction or predicate representing an arbitrary binder matrix.

## 3. Finite comprehension reconstructs C5 and Atomicity

The finite instances of boxed Infinitary Comprehension are strong comprehension SC. For a finite expression $`M`$ of relational type $`\rho`$, saturate its output by a finite tuple $`\bar y`$ and use SC on $`M[\bar y]`$. Boxed universal instantiation and relational Intensionality turn the resulting necessary coextension into a strict application identity for its representative.

This supplies the prerequisites of the [finite λ-free reconstruction](lambda-free-reconstruction.md), §§1–6. Its bracket abstraction, substitution coherence and logical-object definitions recover C with its original H-theoremhood restriction. If the modal operation $`b^{tt}`$ is not primitive, SC first represents the finite matrix $`p=\top`$; similarly, each required Boolean or quantifier object receives its own finite SC definition. No selecting function is needed: each finite derivation uses finitely many definitions, with witnesses eliminated by the reconstruction theorem.

The quantifier equations already yield predicate-form BF. If $`Fx=\top`$ for every $`x`$, then $`O(Fx)=\top`$ for every $`x`$ and every observer qualified at the input type. Quantifier preservation makes $`O(\forall x\, .\,Fx)`$ true. Separation from $`\top`$ gives $`(\forall x\, .\,Fx)=\top`$. After the finite reconstruction, arbitrary finite binder matrices have predicate representatives, so this is the usual BF schema.

Endpoint contrast yields $`\mathrm{ND}_t`$. If $`p\ne q`$, separation supplies an observer whose outputs have different truth values; endpoint range identifies them with opposite endpoints. Necessity of identity follows without abstraction: substituting an equality into reflexivity and using necessitated reflexivity gives $`x=y\to\Box(x=y)`$. Hence both endpoint identities persist. Necessitated equality congruence, together with K, then gives $`\Box(p\ne q)`$. This never necessitates a chosen observer's qualification as a temporary assumption.

In the recovered C, BF and $`\mathrm{ND}_t`$ give C5. Identity judgments at every original type are consequently endpoints: identity gives the top case, and necessary distinctness gives the bottom case. Top-fixing and negation preservation make the same observers fix both endpoints. Therefore their translated equality clauses follow:

```math
\forall x\, .\,O(x=x),\qquad
\forall x,y,F\, .\,[O(x=y)\to(O(Fx)\to O(Fy))].
```

For the substitution clause, an accepted identity cannot be bottom; it is therefore top, whence $`x=y`$, and ordinary substitution identifies the outputs. Section 4 upgrades the qualification to the original whole-operation identities. The established [endpoint characterization](logical-observer-hierarchy.md), §3, now supplies Atomicity at $`t`$ and its C5 consequences.

This proves the finite intermediate characterization: the stated λ-free base with endpoint separation and SC reconstructs C5 + Atomicity at $`t`$. Conversely C5 + Atomicity supplies SC and the required endpoint observers. Neither result assumes abstraction on the λ-free side.

## 4. Whole-operation identities without λ notation

Whole-operation preservation can itself be written λ-free. For negation, bind two operations $`L,R^{tt}`$ and require

```math
\exists L,R^{tt}\, .\,\left[
\forall p\, .\,Lp=O(\neg p)\ \land\
\forall p\, .\,Rp=\neg Op\ \land\ L=R
\right].
```

Use the corresponding finite-arity representatives for the other Boolean clauses. For the universal clause, the two operations have type $`(\sigma t)t`$, with application laws $`LF=O(\forall x\, .\,Fx)`$ and $`RF=\forall x\, .\,O(Fx)`$, and are required to be identical.

These representative clauses imply the pointwise object identities by substitution. Conversely, finite SC supplies the representatives with strict application laws; derived Functionality identifies each pair. Thus the two qualifications are equivalent within the package. Only finitely many representatives are needed for each finite tested-type list. This retains whole-operation preservation without assuming the missing logical objects or a Choice principle.

## 5. Full representation in ZF

An equality matrix in boxed Infinitary Comprehension gives

```math
\exists R^{\sigma t}\, .\,\Box\forall x^\sigma\, .\,
\left(Rx\leftrightarrow\bigvee_{i\in I}x=a_i\right).
```

T follows immediately from $`\Box A=(A=\top)`$ and equality substitution, so these instances give unboxed range comprehension. Section 3 gives H with full endpoint separation. The [intrinsic representation theorem](intrinsic-observer-axioms.md), §§3–5, therefore applies: range comprehension represents every external atom-family, Boolean Completeness joins it, and joins of singleton world–argument supports represent every subset and every existing allowed function.

The representation uses all proposition atoms as worlds and the unique currently true atom as the actual world. For quotient domains, index every raw representative above the desired subset, rather than choosing representatives. Faithfulness makes each inverse support class unique, so Replacement supplies the inverse maps. All these steps work in ZF.

The resulting original typed reducts are exactly, up to canonical typed representation,

```math
D_e=E,\qquad D_t=\mathcal P(W),\qquad
D_{\sigma\rho}=D_\rho^{D_\sigma}\quad(\rho\ne e),
```

for nonempty sets $`E,W`$ and a designated $`w_0\in W`$. Conversely full hierarchies have the endpoint readers and all representatives required by boxed Infinitary Comprehension; well-founded satisfaction recursion interprets the matrices. This converse is also choice-free.

It is enough to use one boxed disjunctive-comprehension schema whose matrices are arbitrary set-indexed disjunctions of finite matrices. Singleton families supply SC, and disjunctions of equality matrices supply range comprehension. No separate finitary-comprehension or λ-closure axiom is needed in either formulation.

Infinity and Extensionality remain optional. Functional Choice holding in every full hierarchy is equivalent to ambient AC over ZF, as proved in the intrinsic note, §6. The theorem characterizes models and canonical expansions; it is not completeness of a deduction calculus for all full-standard validities.

## 6. Why unboxed range comprehension alone is insufficient here

The distinction from the over-H formulation is witnessed by the rigid-output construction. Let $`W=\{0,1\}`$, $`D_e=\{*\}`$ and $`D_t=\mathcal P(W)`$. Recursively set

```math
D_{\sigma t}=\{f:D_\sigma\to\{\varnothing,W\}\},\qquad
D_{\sigma\rho}=D_\rho^{D_\sigma}\quad(\rho\ne t,e).
```

Application is evaluation; the primitive formula constructors and binders have ordinary worldwise truth conditions. Identity is constant equality and necessity ranges over both worlds. The two readers $`O_w(p)=W`$ when $`w\in p`$, and $`O_w(p)=\varnothing`$ otherwise, are admitted operations.

Each reader satisfies the strict Boolean laws. For any admitted predicate $`F`$, every value $`Fx`$ is an endpoint. Hence its quantified meet or join is an endpoint too, and the readers preserve both binders at every input type. They jointly separate propositions; ordinary function extensionality at higher types gives full typed separation. Their particular Boolean and quantifier composite operations are endpoint-valued maps, so the representative version of qualification is satisfied as well.

Every external subset of every typed domain has its rigid characteristic property. Thus unrestricted unboxed range comprehension holds at both worlds. But every admitted $`R^{tt}`$ is endpoint-valued. None can agree necessarily with a contingent $`p=\{0\}`$, so

```math
\exists R^{tt}\, .\,\Box\forall p\, .\,(Rp\leftrightarrow p)
```

fails. Even this finite SC instance is missing. The construction does not have a first-class negation object with its full application law; such logical objects were not premises of the stated λ-free base. It therefore does not refute a formulation that independently postulates them.

## Sources

- [Finite λ-free reconstruction](lambda-free-reconstruction.md), §§1–6: bracket abstraction and the finite C translation; OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026, `misc`, unpaginated.
- [Logical observer hierarchy](logical-observer-hierarchy.md), §3: endpoint separation and C5 + Atomicity; OpenAI Codex, prompted by Daniel Kodsi, 23–24 October 2026, `misc`, unpaginated.
- [Intrinsic observer axioms](intrinsic-observer-axioms.md), §§3–7: full representation in ZF, scope and the AC comparison; OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, `misc`, unpaginated.
- The construction in §6 extends the rigid-output example in *Infinitary extension comprehension and lambda-free Comprehension*, §4, OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026, `misc`, unpaginated. Its domains and the additional observer verification are reproduced above.
