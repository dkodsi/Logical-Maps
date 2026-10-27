# CH continuation: Boolean completion and persistent comparison witnesses

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated. No native records, formal-verification statuses, or source proofs are changed.

**Result and remaining issue.** Every qualified observer in a C5 Henkin model extends to a complete homomorphism of the external Boolean completion. Necessary OS makes the extended observers cover every nonzero element of that completion. Thus failure of external Boolean completeness is not the obstruction to extending the earlier CH argument. The remaining obstruction is the interpretation of the higher Henkin domains. A separate native theorem makes existential relation assertions over persistent base predicates noncontingent; injections and bijections between persistent carriers are instances.

## 1. The semantic reduction and what C5 adds

Use the [observer-monoid representation](../../../next-update/proofs/observer-shift-semantics.md), §§5–8. After taking actual identity quotients and, if needed, an elementary extension, the proposition domain is a Boolean algebra B, higher domains consist of actual functions, admitted quantifiers are Boolean infima and suprema, and the observers preserve their admitted families. The representation does not fill any higher function domain.

C5 makes every object-identity proposition an endpoint. Accordingly native Box is the global top test in this Boolean presentation. Qualification at t implies qualification at every requested finite type list. We can therefore use the external set $`\mathcal E`$ of all admitted $`\mathrm{Good}_{\{t\}}`$ observers without introducing an object-language infinite qualification conjunction.

The existing [canonical-adjoint theorem](../../../classicism-results-2026-10-24-v2/proofs/h-observer-space/canonical-adjoints-and-image-factorization.md), §§2–4, supplies admitted maps

```math
L_E\dashv E\dashv R_E.
\tag{1}
```

These are actual adjunctions on the external Boolean order of B: their equivalences hold for every pair of objects of B. Consequently E preserves **every externally existing** join and meet in B, not only the families whose indexing maps are admitted. For example, if $`b=\bigvee X`$ exists in B and u bounds all $`E(x)`$, then $`x\le R_E(u)`$ for all $`x\in X`$, whence $`b\le R_E(u)`$ and $`E(b)\le u`$. Thus $`E(b)=\bigvee E[X]`$. The other adjunction gives meets.

This corrects a tempting but invalid objection to completion: qualification alone is initially stated for admitted families, but its canonical adjoints have the stronger external order consequence (1).

## 2. Complete extensions and preservation of the observer cover

Let $`\overline B`$ be the Boolean, equivalently MacNeille, completion of B, identifying B with its dense Boolean subalgebra. For each E define

```math
\overline E(x):=
\bigvee^{\overline B}\{E(b):b\in B, b\le x\}.
\tag{2}
```

**Completion lemma.** This is the unique unital complete Boolean homomorphism extending E. Injectivity of E is unnecessary.

First, every maximal antichain of B has join one in B, so §1 says its E-images have join one as well. More generally E preserves any antichain join that exists in B. Given $`x\in\overline B`$, choose a maximal B-antichain refining the two pieces x and ¬x. It has join one; its image pieces are disjoint and still join to one. Formula (2) therefore gives
$`\overline E(\neg x)=\neg\overline E(x)`$.

For arbitrary $`(x_i)_{i\in I}`$ in $`\overline B`$, monotonicity gives
$`\bigvee_i\overline E(x_i)\le\overline E(\bigvee_i x_i)`$.
For the reverse, fix $`b\in B`$ below $`\bigvee_i x_i`$. The B-elements lying below some $`b\land x_i`$ are dense below b. Choose a maximal antichain among them. Its join in B is b; §1 makes the join of its E-images equal E(b), and each such image lies below some $`\overline E(x_i)`$. Thus $`E(b)\le\bigvee_i\overline E(x_i)`$. Taking the join over b proves the reverse inequality. Endpoints follow directly, and complements together with arbitrary joins give complete Boolean preservation. Density gives uniqueness. The antichain choices here are ordinary external ZFC metatheory, not object-language Choice.

Now assume □$`S_{t,\{t\}}`$. For each $`b\in B`$, $`b>0`$, the exact separation formula gives

```math
\bigvee_{E\in\mathcal E}^{B} E(b)=1_B.
\tag{3}
```

This join already exists in B: it is the admitted existential value of
$`\exists E\,[\mathrm{Good}_{\{t\}}(E)\land E(b)]`$.
Qualification is endpoint-valued under C5. Necessary separation says that this value is Top whenever b is nonbottom. The embedding into the completion preserves (3).

For any $`0<x\in\overline B`$, choose $`0<b\in B`$ below x. Monotonicity and (3) yield

```math
\boxed{\bigvee_{E\in\mathcal E}^{\overline B}\overline E(x)=1_{\overline B}.}
\tag{4}
```

Thus the observer cover survives completion, including at the newly added Boolean elements.

This does **not** turn the original model into an internally full Boolean hierarchy. Keeping the old typed quantifier domains preserves all old formula values in the complete ambient truth algebra, because their existing meets and joins are preserved. But the native proposition sort still ranges over the old B. Adding all of $`\overline B`$ to that sort requires extending function domains and changing higher quantifier domains. Filling the hierarchy gives a full Boolean-valued structure with the algebraic cover (4); passage to an ordinary pointed C-model additionally needs a justified internal-model and generic-truth construction of the kind used in the earlier forcing notes. Neither that passage nor agreement of the new CH proposition with the original Henkin one follows from completion. The earlier full-forcing CH theorem applies only once its own internally full semantic hypotheses have been supplied.

The concrete mathematical gap remains: a field complete relative to the old admitted subproperties may cease to be complete after filling those domains, and new subsets or injections may change the native CH assertion. Neither the adjoints nor (4) proves that this filling is elementary for the analytical fragment.

## 3. A native persistence theorem for existential relation witnesses

Fix a finite qualification list Δ and define

```math
\mathrm{Sub}_\Delta(p):=
\forall E^{tt}\,[\mathrm{Good}_\Delta(E)\to E(p)\le p],
\tag{5}
```

where the inequality is Boolean order, hence an identity judgment. Under C5, qualification is equivalent to its finite collection of whole-operation identities; the translated equality clauses follow from its Boolean clauses. Qualification and the displayed order judgments are therefore endpoints. BF then makes $`\mathrm{Sub}_\Delta(p)`$ itself an endpoint, in particular persistent.

There is an elementary C consequence

```math
S_{t,\Delta}\land\mathrm{Sub}_\Delta(p)\land p\ne0
\quad\longrightarrow\quad p.
\tag{6}
```

For if p is false, every qualified E(p) is false by the order inequality. Separation from zero then gives p=0, a contradiction. Necessitate the **closed theorem** (6), not any optional premise. Under C5, $`\mathrm{Sub}_\Delta(p)`$ and $`p\ne0`$, when true, supply their own boxes. The explicit premise □$`S_{t,\Delta}`$ therefore gives □p. We obtain the exact criterion

```math
\boxed{C5+\Box S_{t,\Delta}\ \vdash\
\mathrm{Sub}_\Delta(p)
\ \longleftrightarrow\ (p=0\lor p=1).}
\tag{7}
```

The converse just uses endpoint fixing. Current separation alone gives (6), not the endpoint conclusion (7).

Here is a useful sufficient grammar for (5). Let $`\vec A`$ be persistent relation predicates, and put

```math
p(\vec A)=\exists R_1\cdots R_n\;	heta(\vec R,\vec A).
\tag{8}
```

The matrix is built using Boolean operations and ordinary quantifiers. Its nonlogical predicate heads are precisely the displayed witnesses $`R_i`$ and the persistent predicates $`A_j`$; identity tests between witness-free object terms are allowed. Witnesses occur as predicate heads, not as opaque arguments to other predicates. Other quantified variables may serve as arguments or as operations inside witness-free argument terms. Include all exposed binder types in Δ, or use qualification at t and its C5 reduction theorem.

Persistence over C5 makes every value of every $`A_j`$ an endpoint. Whole observer identities, endpoint fixing and C5 Functionality give

```math
E(p)=\exists R_1\cdots R_n\;
\theta(\vec R^{,E},\vec A),
\qquad
R_i^{,E}[\vec x]=E(R_i[\vec x]).
\tag{9}
```

Each transformed witness is admitted by lambda abstraction. The H-valid existential introduction from the right side of (9) to (8) has its necessary form in C, so (9) gives the Boolean inequality $`E(p)\le p`$. This proves (5), with no choice of preimages and no claim that E is onto. Equation (7) now makes p an endpoint under necessary separation.

In particular, for persistent carriers X and Y, expressed at any admitted argument types,

```math
\exists R\,[R:X\hookrightarrow Y],
\qquad
\exists R\,[R:X\cong Y]
\tag{10}
```

are each equivalent to their own box and diamond under C5 + □OS. The matrix saying that a binary relation is a total injective function, or a bijection, contains only carrier membership, applications of R and equality of its arguments, so it has exactly grammar (8). This preserves the **existence** of a witness, not necessarily one chosen graph. Relational Choice has not been assumed.

## 4. Persistent labels compared with any real carrier

The existential-witness theorem also compares a persistent carrier with the reals without requiring a persistent real carrier. Fix a Frege arithmetic at a type κ and assume its nondegeneracy clause $`I^*_\kappa`$. This clause, numberhood, and the arithmetic relations are endpoints under C5 by [the arithmetic audit](arithmetic-audit.md), §2. The guard is explicit: Frege arithmetic at an arbitrary type need not be nondegenerate.

Write $`\nu=(\kappa t)t`$. Standard integer and rational codes can be represented by natural-number codes at ν, with an arithmetically defined predicate Q and order $`<_Q`$. For example, use a signed coprime numerator and positive denominator, with one normalized code for zero, and a fixed arithmetic pairing convention. These are rigid predicates by arithmetic invariance. Equivalently one can retain finite tuples of natural-number variables throughout; no new quotient sort or operation type is needed.

For a persistent $`Z^{\zeta t}`$, let $`\mathrm{CutFam}(Z)`$ say that there is an admitted $`C^{\zeta\nu t}`$ such that, for each z in Z, its slice $`C_z`$ is a nonempty proper downward closed subset of Q with no greatest member, and any two distinct labels in Z have different slices. Distinctness can be stated as

```math
\forall z,z'\in Z\;[z\ne z'\to
  \exists q\in Q\;(Czq\mathbin{\not\leftrightarrow}Cz'q)].
\tag{11}
```

Every quantifier after the initial existential C is an ordinary object quantifier. Its matrix uses only applications of C, fixed arithmetic predicates, Z, and identity. Thus §3 gives

```math
C5+\Box OS+I^*_\kappa
\quad\vdash\quad
\mathrm{CutFam}(Z)\leftrightarrow
\Box\mathrm{CutFam}(Z).
\tag{12}
```

For any admitted real structure $`\mathfrak R`$ with carrier X, the ordinary internal real-categoricity argument gives

```math
\mathrm{Real}(\mathfrak R)\quad\Longrightarrow\quad
\bigl(\mathrm{CutFam}(Z)
\leftrightarrow\exists F\,[F:Z\hookrightarrow X]\bigr).
\tag{13}
```

Here the number predicate in the real structure and the guarded Frege numbers are both inductive Peano structures. Their unique arithmetic isomorphism is admitted: define the least relation on pairs containing the two zeroes and closed under simultaneous successor, then prove totality and functionality by the two induction principles. This also defines the interpretation of the rational codes in the field. It is a relational construction and does not require a chosen map-valued object.

For the forward direction of (13), interpret each rational cut in X. Its rational image is an admitted subproperty, is nonempty and bounded above, and therefore has a unique supremum. Define F(z,x) by the formula saying that x is this supremum. Lambda abstraction supplies one graph simultaneously for all z; unique suprema give totality and functionality. Rational density and the absence of a greatest cut member show that different cuts have different suprema. The reverse direction takes the rational lower cut of each image real. Those cuts are nonempty and proper by Archimedeanness, and rational density makes distinct image reals yield different cuts. Archimedeanness and density are the usual internal consequences of the stated nonempty bounded completeness axiom. No selection from a family of nonunique witnesses is used.

Consequently, whenever real structures exist, the comparison “Z injects into the real carrier” is governed by the single endpoint proposition (12), independently of which real structure is selected. This result supplies an invariant comparison with the reals; it does not supply an invariant well-order or a rigid copy of every subset of the reals. For an application omitting the explicit arithmetic guard, one must additionally justify the needed $`I^*_\kappa`$ at the chosen base type.

## 5. A persistent cardinal-gap certificate for necessary failure of CH

Keep the arithmetic guard $`I^*_\kappa`$ and write N for its persistent Frege number carrier. Write $`\mathrm{Inj}(V,W)`$ for existence of an admitted relational injection. Let Z and Y be persistent carriers, possibly at different admitted argument types. Then

```math
\boxed{\begin{gathered}
C5+\Box OS+I^*_\kappa,\qquad
\mathrm{CutFam}(Z),\quad\mathrm{CutFam}(Y),\\
\neg\mathrm{Inj}(Z,N),\qquad
\neg\mathrm{Inj}(Y,Z)
\quad\Longrightarrow\quad
\Box U_{\sigma,\neg\mathrm{CH}}
\end{gathered}}
\tag{14}
```

for every admitted target real-carrier type σ. No well-order of Z, Y, or the real carrier is assumed. As usual the universal conclusion may be vacuous at a type with no real structure; where one exists it says that structure fails CH.

Here is the current mathematical implication underlying (14). Given a real structure with carrier X, use (13) to obtain injections f:Z→X and g:Y→X. Define its admitted subproperty

```math
A(x):=Xx\land\exists z\in Z\;f(z,x).
\tag{15}
```

The graph f is a bijection Z→A. If A is countable, compose its injection into the field's natural numbers with f and with the arithmetic isomorphism to N; this contradicts $`\neg\mathrm{Inj}(Z,N)`$. If A is bijective with X, compose g with a bijection X→A and the inverse relation of f; this contradicts $`\neg\mathrm{Inj}(Y,Z)`$. Thus both alternatives in native CH fail for this A. All images, inverses, and composites here are lambda-defined relations; the argument makes only finitely many existential witness eliminations and requires no Choice principle.

For the modal conclusion, §3 makes each injection-existence assertion an endpoint, hence also makes its negation an endpoint. Section 4 does the same for each cut-family assertion, and C5 makes the arithmetic guard an endpoint. Necessitate the closed current implication just proved and apply these boxed premises. This proves (14) without necessitating an optional assumption.

**Dedekind-finite label case.** Take Y=N. Its cut family is the arithmetic graph assigning n the rational lower cut at n. Consequently any persistent Z satisfying

```math
\mathrm{CutFam}(Z),\qquad
\neg\mathrm{Inj}(Z,N),\qquad
\neg\mathrm{Inj}(N,Z)
\tag{16}
```

forces necessary failure of CH at every target real type. In the finite-support Cohen hierarchy, the coordinate labels form such a persistent carrier whenever that label orbit is included in the typed base domain. Their pairwise distinct Cohen real names give the cut family. The familiar finite-support argument prevents injections in both directions between that coordinate orbit and N. Thus a common supported lottery retaining these labels cannot combine this component with a CH-true component while satisfying □OS. Unlike the bounded-stage obstruction, this consequence does not require a target-stage filtration or restrictions on how target automorphisms move stages.

The general form (14) also excludes a source whose Z is Dedekind infinite, if an additional persistent Y with the stated two properties is available. The stage-independent Cohen obstruction, §§1–5, now supplies such a Y explicitly: the crisp unordered pairs of Cohen coordinate labels. Two finite transposition arguments exclude Y→Z for every supported graph, and lexicographically sorting and interleaving the two Cohen reals gives its distinct-cut family. This works for an arbitrary independent auxiliary forcing and any allowed coordinate support leaving an infinite fresh tail. It needs neither countability of the supports nor any stage-preservation condition on target automorphisms. No persistent carrier of all symmetric reals is assumed.

## 6. Consequences for the CH search

Equations (7)–(10) are a native counterpart of the forcing-persistent-witness argument. They transfer cardinal comparisons when the compared carriers have persistent membership. They do not by themselves produce rigid copies of arbitrary carriers or well-orders.

In particular, a well-ordering condition quantifies over arbitrary subproperties and uses those bound properties as predicate heads. That universal second-order clause is outside (8). The direct theorem must not be used to assert that every possibly available well-order, every current real carrier, or every Dedekind-completeness assertion is observer-subinvariant.

The new complete-algebra reduction removes one apparent difficulty, but leaves precisely this higher-domain issue. A general CH proof needs either a native cardinal comparison reduction that avoids replacing the admitted predicate domains, or a justified interpretation of all the needed carrier and well-order witnesses. A countermodel must instead preserve the observer cover and lambda/quantifier closure while arranging different admitted subsets or injection graphs over its real carriers. No such CH countermodel or unrestricted CH proof is supplied by this continuation.

No Lean, compilation, native-record editing, or full-function-domain assumption is used.
