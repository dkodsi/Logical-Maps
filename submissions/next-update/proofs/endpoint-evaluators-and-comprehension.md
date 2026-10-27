# Correct endpoint evaluators, completeness and comprehension

One admitted operation reading current truth supplies explicit witnesses for several established connections. The direct construction from Boolean Completeness needs only the tt instance and ND at t. Over C5, the same evaluator unifies Actuality, completeness, Plenitude and Rigid Comprehension.

## 1. Correct evaluation and Actuality

Work in the fixed relational C. Define

```math
\mathrm{Correct}(E):=\forall p^t\, .\,
(p\to Ep=\top)\land(\neg p\to Ep=\bot)
```

This asks for correct endpoint outputs at current inputs. It does not impose the logical-observer qualification. Over C,

```math
\exists E^{tt}\, .\,\mathrm{Correct}(E)
\quad\Longleftrightarrow\quad
\mathrm{Actuality}+\mathrm{ND}_t
```

Given such an $`E`$, put $`a_E:=\forall p\, .\,Ep\to p`$. This is true. If $`p`$ is true, $`Ep=\top`$, and universal instantiation gives $`a_E\le(Ep\to p)=p`$. Thus $`a_E`$ is an Actuality witness.

Correctness also gives all-type ND. For distinct $`x,y`$, $`E(x=y)=\bot`$ and $`E\top=\top`$. NI preserves both identities. Necessitate the unconditional C theorem $`x=y\to(x=y)=\top`$. If the objects could coincide, application would identify the two necessarily opposite outputs. Hence their distinctness is necessary. This uses no BF.

Conversely, let $`a`$ witness Actuality and assume ND at t. Define $`E(p):=\Box(a\to p)`$. For a true $`p`$, Actuality gives $`a\le p`$, and NI makes that entailment proposition Top. For a false $`p`$, Actuality gives $`a\le\neg p`$; since $`a`$ is nonbottom, $`a\le p`$ fails. ND at t makes the failed identity defining that entailment necessarily false, so $`Ep=\bot`$. Thus $`E`$ is correct.

## 2. Boolean Completeness constructs the evaluator

**Theorem.**

```math
\mathrm C+\mathrm{ND}_t+\mathrm{BC}_{tt}
\quad\vdash\quad\exists E^{tt}\, .\,\mathrm{Correct}(E)
\quad\vdash\quad\mathrm{Actuality}
```

Here $`\mathrm{BC}_{tt}`$ is Boolean Completeness at the type of properties of propositions. For $`p^t`$, put

```math
h_p:=\lambda r^t\, .\,r=p,\qquad
H:=\lambda h^{tt}\, .\,\exists p^t\, .\,p\land h=h_p
```

The current members of the admitted family $`H`$ are exactly the haecceities of currently true propositions. Let $`E^{tt}`$ be their algebraic join, supplied by completeness in its dual form.

If $`q`$ is true, $`h_q\le E`$. Evaluation at $`q`$ gives $`\top=h_q(q)\le E(q)`$, hence $`E(q)=\top`$.

If $`q`$ is false, put $`K_q:=\lambda r\, .\,r\ne q`$. Every true $`p`$ differs from $`q`$, and ND gives $`\Box(p\ne q)`$. Necessitating the unconditional substitution theorem

```math
p\ne q\to\forall r\, .\,(r=p\to r\ne q)
```

gives the whole relation entailment $`h_p\le K_q`$. This does not collect pointwise identities through BF. Hence $`K_q`$ bounds the entire current family, $`E\le K_q`$, and evaluation at $`q`$ gives $`E(q)\le\bot`$. The evaluator is correct; §1 gives Actuality.

The global BC + ND consequence was already derivable through Vicinity and Weakly Inextensible Comprehension. The contribution is the direct witness and its precise type scope. No BF, OS or Plenitude premise is used.

## 3. The same join at every relational type

Fix $`\tau=\sigma_1\cdots\sigma_n t`$. Assume BC at $`\tau`$ and ND at the argument types. For $`X^\tau`$, form

```math
h_{\bar x}:=\lambda\bar z\, .\,\bigwedge_i z_i=x_i,\qquad
H_X:=\lambda Z^\tau\, .\,\exists\bar x\, .\,X[\bar x]\land Z=h_{\bar x}
```

Let $`Y`$ be the join of this admitted family. The same argument proves

```math
X[\bar u]\to Y[\bar u]=\top,\qquad
\neg X[\bar u]\to Y[\bar u]=\bot
```

For the second implication, use the complement of the haecceity of $`\bar u`$ as a bound. Any current X-tuple differs in some coordinate, whose ND instance makes the tuple difference necessary. The necessitated finite-tuple substitution theorem supplies the whole bound.

The endpoint outputs give weak persistence. For weak inextensibility, suppose every current Y-tuple necessarily satisfies $`Z`$. Every X-tuple $`\bar u`$ is a Y-tuple, so $`\Box Z[\bar u]`$. Equality substitution makes $`h_{\bar u}\le Z`$. Thus $`Z`$ bounds $`H_X`$, and the join property gives $`Y\le Z`$.

Weak rigidity gives persistence by applying weak inextensibility to $`\lambda\bar z\, .\,\Box Y[\bar z]`$, using weak persistence and axiom 4. This is the persistent formulation of Weak Rigid Comprehension used in the database. At the empty tuple, use Top or Bottom according to the truth of $`X`$.

Thus full BC + ND gives Weak Rigid Comprehension directly; the established Weak Rigid Comprehension + ND implication then gives Plenitude. This construction does not establish the outer box required for full inextensibility, so it does not yield Rigid Comprehension under these premises alone.

## 4. One evaluator supplies three constructions over C5

Under C5 + Actuality, §1 supplies a correct evaluator. BF makes quantifiers infima or suprema of admitted ranges. For example, a lower bound $`b`$ of every $`Fx`$ gives $`\forall x\, .\,\Box(b\to Fx)`$; BF and fixed-parameter distribution give $`b\le\forall x\, .\,Fx`$. The relational version uses the relevant BF instances and Functionality.

**Boolean Completeness.** For a current family $`F^{\tau t}`$, $`\tau=\bar\sigma t`$, define

```math
G_F[\bar z]:=\forall Y^\tau\, .\,E(FY)\to Y[\bar z]
```

For a current member $`Y`$, its guard is Top, so $`G_F\le Y`$. If $`V`$ bounds every current member, each guard is either Top with $`V\le Y`$, or Bottom with the implication Top. The range-infimum property gives $`V\le G_F`$. Thus this is the required greatest lower bound. Existential quantification with conjunction gives the dual join.

**Plenitude.** For a currently functional graph $`U^{\sigma\tau t}`$, $`\tau=\bar\rho t`$, define

```math
g_U(x)[\bar z]:=\exists Y^\tau\, .\,E(U[x,Y])\land Y[\bar z]
```

Fix $`x`$ and its unique current output $`A`$. Correctness makes the guard Top exactly at $`Y=A`$. The range-supremum property gives $`g_U(x)[\bar z]=A[\bar z]`$; Functionality gives $`g_U(x)=A`$. This is an admitted representing operation at every permitted relational output type.

**Rigid Comprehension.** Put

```math
R_X[\bar z]:=E(X[\bar z])
```

It is currently coextensive with $`X`$. NI makes its endpoint identities necessary, and BF collects them into necessary universal endpoint-valuedness. Endpoint-valuedness plus BF implies weak rigidity: weak persistence is immediate; for weak inextensibility, each endpoint case gives the necessary implication to the proposed bound, and BF combines these into relation entailment. C5 supplies necessary BF. Necessitate this finite-premise implication and apply it to the necessary endpoint and BF premises. The result is necessary weak rigidity, hence the required rigidity of $`R_X`$.

The Boolean Completeness construction avoids using Rigid Comprehension as an intermediate theorem. The rigidity construction itself shares the substance of the existing proof; the gain is the common evaluator.

## 5. The resulting equivalence

Plenitude at $`(t,t)`$ represents the graph assigning Top to true propositions and Bottom to false ones, so it supplies a correct evaluator. Conversely, over C5 the evaluator supplies full Plenitude, completeness and Rigid Comprehension by §4. Full Rigid Comprehension implies Actuality by its existing theorem; full completeness includes the tt instance. Therefore over C5,

```math
\begin{aligned}
\mathrm{Actuality}
&\Longleftrightarrow\exists E^{tt}\, .\,\mathrm{Correct}(E)
\Longleftrightarrow\mathrm{BC}_{tt}\\
&\Longleftrightarrow\mathrm{Boolean\ Completeness}
\Longleftrightarrow\mathrm{Plenitude}_{t,t}\\
&\Longleftrightarrow\mathrm{Plenitude}
\Longleftrightarrow\mathrm{Rigid\ Comprehension}
\end{aligned}
```

These are current principles. This package need not imply OS or global Atomicity: the established qualitative-contrast model at its restricted object is a counterexample. A correct evaluator need not preserve every quantifier as a whole-operation identity.

## Sources

Direct evaluator construction, type refinements and unified presentation: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), *Lattice and comprehension proof comparison*, §§2–6, unpaginated. [Source hashes](../evidence/source-manifest.json) · [Review evidence](../evidence/proof-reviews.json).

The all-schema arrows and their original attributions are retained. Relevant records include `c5-and-completeness-imply-actuality`, `c5-and-completeness-imply-plenitude`, `c5-and-actuality-imply-completeness`, `c5-and-actuality-imply-rigid-comprehension`, `plenitude-r-implies-actuality`, `plenitude-r-implies-distinctness-necessary-r`, and `weak-rigid-comprehension-and-nd-imply-plenitude`. The underlying BC + Actuality haecceity-join argument is Bacon and Dorr's; here ND supplies the exclusion of extra current tuples instead.
