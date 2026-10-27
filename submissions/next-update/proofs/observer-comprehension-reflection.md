# Logical observers reflect persistent and rigid comprehension

25 October 2026. OpenAI Codex, prompted by Daniel Kodsi. Direct source for the new transport arguments: `misc`, this note, unpaginated. Earlier results and constructions retain the attributions below.

**Result.** C5 plus ordinary logical separation turns every assumed Rigid Comprehension instance into its necessary form. There is a stronger, finite local statement: current Necessity of Distinctness at the proposition type, together with one suitable propositional separation instance, suffices. The same argument applies separately to Persistent Comprehension and Gallin Extensional Comprehension. It works because the witnesses supplied by these principles are fixed by every qualifying observer, not because observers are onto.

## 1. Exact language, instances and scope

Work in fixed relational C. Fix a finite, possibly empty, argument tuple of admitted types

```math
\bar\sigma=(\sigma_1,\ldots,\sigma_n),\qquad
\tau=\sigma_1\cdots\sigma_n t
```

The zero-argument case is $`\tau=t`$. Every type displayed is admitted; individual types may occur among the arguments. Define

```math
\mathrm{Coext}_\tau(X,Y):=
\forall\bar x\,[X[\bar x]\leftrightarrow Y[\bar x]]
```

For a qualification $`Q(Y)`$, put

```math
\mathrm{Comp}_{Q,\tau}:=
\forall X^\tau\exists Y^\tau
\,[Q(Y)\land\mathrm{Coext}_\tau(X,Y)]
\tag{1}
```

The three qualifications of interest are exactly the recorded ones:

```math
\begin{aligned}
P(Y)&:=\Box\forall\bar x\,[Y[\bar x]\to\Box Y[\bar x]],\\
I(Y)&:=\Box\forall Z^\tau
\,[(\forall\bar x\,[Y[\bar x]\to\Box Z[\bar x]])\to Y\le Z],\\
R(Y)&:=P(Y)\land I(Y),\\
G(Y)&:=P(Y)\land P(\neg Y)
\end{aligned}
\tag{2}
```

Thus the cases of (1) are Persistent, Rigid and Gallin Extensional Comprehension. In particular, inextensibility has its outer box; no weak variant is substituted.

Use the whole-operation qualification $`\mathrm{Good}_\Delta(E)`$ in [Logical observer separation and its hierarchy](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1. Let

```math
\Delta\supseteq\{\tau,\sigma_1,\ldots,\sigma_n\}
\tag{3}
```

be one finite external type list. The only separation premise needed is

```math
S_{t,\Delta}:\quad
\forall p,q^t\left[p=q\leftrightarrow
\forall E^{tt}\bigl(\mathrm{Good}_\Delta(E)
\to(Ep\leftrightarrow Eq)\bigr)\right]
\tag{4}
```

The smaller modal premise is the unboxed, currently asserted formula

```math
\mathrm{ND}_t:=
\forall p,q^t\,[p\ne q\to\Box(p\ne q)]
\tag{5}
```

Neither (4), (5), nor comprehension is assumed necessary. The result remains a formula-by-formula schema; there is no type quantifier or infinitary conjunction in the object language.

## 2. Two fixed-value lemmas

**Lemma 1.** Over C + ND_t, every native boxed proposition is one of the Boolean endpoints. Consequently every Good observer fixes it:

```math
E(\Box q)=\Box q
\tag{6}
```

Proof. By definition $`\Box q`$ is the identity proposition $`q=\top`$. If this identity is true, Necessity of Identity makes it necessary, so $`\Box q=\top`$. If the identity is false, ND_t makes its negation necessary; the C equivalence $`\Box\neg r\leftrightarrow r=\bot`$, applied to $`r=\Box q`$, gives $`\Box q=\bot`$. Every Good observer fixes Top and Bottom over C. This proves (6) by cases. The argument uses current ND_t and NI, without necessitating ND_t.

**Lemma 2.** Already over C, persistence of a relation implies

```math
P(Y)\quad\Longrightarrow\quad
\forall\bar x\,[Y[\bar x]=\Box Y[\bar x]]
\tag{7}
```

Proof. Apply CBF successively to the outer box in P(Y). For each current tuple this gives $`\Box(Y[\bar x]\to\Box Y[\bar x])`$. The reverse implication $`\Box Y[\bar x]\to Y[\bar x]`$ is an unconditional instance of T, hence is necessary. Combining the necessary implications and using C's propositional Intensionality gives (7). For an empty tuple CBF is unused. No Barcan formula is needed: only the converse Barcan theorem of C is used here.

Together, (6) and (7) yield

```math
P(Y)\quad\Longrightarrow\quad
\forall\bar x\,[E(Y[\bar x])=Y[\bar x]]
\tag{8}
```

for each Good E. Thus each persistent witness is fixed pointwise. We do not assert a whole identity of relations from pointwise identity, which would require a separate Functionality argument; the pointwise statement is sufficient below.

Moreover, each of P(Y), R(Y) and G(Y) is a native boxed proposition or a finite Boolean combination of boxed propositions. By Lemma 1 and Boolean preservation,

```math
E(Q(Y))=Q(Y)\qquad(Q=P,R,G)
\tag{9}
```

Notice that the quantifiers inside Q(Y) have not been moved through E. We fix the entire boxed condition. This is why they do not enlarge the list (3).

## 3. A reusable reflection theorem with fixed witnesses

Here is the abstract step, separated from the sufficient modal premise. Suppose that for every eligible $`E`$, a qualification $`Q(Y)`$ satisfies

```math
E(Q(Y))=Q(Y),\qquad
Q(Y)\to\forall\bar x\,[E(Y[\bar x])=Y[\bar x]]
\tag{10}
```

These are hypotheses about the actual admitted witnesses and observer actions, not assumptions that E has a right inverse.

**Theorem.** Over C, under (3), (4) and (10),

```math
\mathrm{Comp}_{Q,\tau}
\quad\Longrightarrow\quad
\Box\mathrm{Comp}_{Q,\tau}
\tag{11}
```

Proof. Write A for the closed formula (1), and fix an arbitrary Good_Δ observer E. Its quantifier laws at τ move E through the outer universal and existential. Its Boolean law and the laws at the tuple's argument types then give the identity

```math
E(A)=\forall X^\tau\exists Y^\tau\left[
 E(Q(Y))\land
 \forall\bar x\,[E(X[\bar x])\leftrightarrow E(Y[\bar x])]
\right]
\tag{12}
```

Equation (12) uses only the stipulated whole-operation preservation identities, applied and rewritten in context. In particular it is obtained before using the pointwise witness facts (10). Those facts are used below to establish the current truth of the matrix after the binders have been exposed; they are not promoted to identities of lambda abstractions. Thus this step does not conceal a Functionality or Barcan assumption.

For an arbitrary current X, the lambda term

```math
X^E:=\lambda\bar x.\,E(X[\bar x])
\tag{13}
```

is an admitted relation of exactly the same type τ. In the zero-argument case it is EX. Apply current A to X^E, obtaining an admitted Y with Q(Y) and

```math
\forall\bar x\,[E(X[\bar x])\leftrightarrow Y[\bar x]]
\tag{14}
```

The first condition in (10) makes E(Q(Y)) true. The second replaces the right-hand applications in (14) by E(Y[x̄]). Hence this very Y satisfies the existential matrix in (12). As X was arbitrary, E(A) is true. ETop is also true. This holds for every observer eligible in precisely (4), so separation applied to A and Top gives A=Top, which is □A. This proves (11).

Only the input relation X was transformed. The existential witness is reused unchanged because it is observer-fixed. The proof neither selects preimages under E nor assumes an external reindexing of higher-type domains. All witness-producing applications are to admitted lambda terms and the currently assumed sentence (1).

## 4. Rigid and persistent comprehension become necessary

Lemmas 1–2 verify (10) for every qualification in (2). Therefore, for each fixed τ and finite Δ as in (3),

```math
\boxed{
\mathrm C+\mathrm{ND}_t+S_{t,\Delta}
\quad\vdash\quad
\mathrm{Comp}_{Q,\tau}\to
\Box\mathrm{Comp}_{Q,\tau}
\quad(Q=P,R,G)
}
\tag{15}
```

In particular,

```math
\boxed{\mathrm{C5}+\mathrm{OS}+\mathrm{RC}_\tau
\quad\Longrightarrow\quad\Box\mathrm{RC}_\tau}
\tag{16}
```

This is genuinely instancewise: comprehension at any other relation type is not used. For example, the e→t comprehension instance needs the single separation qualification list {et,e}; the proposition-only case needs {t}. The proof gives the corresponding Persistent and Gallin comprehension conclusions on exactly these lists as well.

An alternative sufficient assumption over bare C is separation by those Good observers that satisfy $`\forall q\,[E(\Box q)=\Box q]`$. The same fixed-witness argument works without ND_t. This is *fixing the values of native boxes*, not the different native-Box commutation law $`E(\Box q)=\Box(Eq)`$. Under ND_t every ordinary Boolean Good observer has the required fixing property by Lemma 1, which recovers (15).

## 5. Relation to existing stronger full-schema consequences

The direct theorem should not be presented as an entirely new full-scope collapse. Several relevant connections were already established:

* The database's `c5-and-persistent-comprehension-imply-gallin` derives Gallin Extensional Comprehension from C5 and full Persistent Comprehension. Its proof makes the persistent complement available.
* `gallin-comprehension-and-bf-imply-rigid-comprehension`, together with C5's necessary Barcan consequence, supplies full Rigid Comprehension. The converse to Persistent Comprehension is immediate and recorded. Thus full Persistent and Rigid Comprehension were already equivalent over C5.
* Full Persistent Comprehension implies Actuality by the recorded source proof. Under C5, the previously established atomic-observer converse takes Actuality and propositional ordinary separation qualified at t to Atomicity_t, hence to the strong endpoint-separation regime. This already supplies numerous necessary structural principles.

Consequently the main explanatory contribution here is the finite, type-local reflection mechanism and its weaker current ND_t hypothesis. It does not require the higher comprehension instance used to derive Actuality, nor full OS, necessary separation, necessary Choice or an atomicity argument.

There is an important limit to the modal weakening. Full OS supplies BF_t, and the recorded `nd-t-and-bf-t-imply-necessary-nd-t` (Classicism Proposition 2.4, p. 23) gives □ND_t from current ND_t and BF_t. The recorded `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` then gives C5. Thus full OS + ND_t is already equivalent to full OS + C5; this is not a new weaker full theory. The exact local theorem (15) remains informative when its list Δ omits t, for example Δ={et,e}. This same finite-list distinction is noted in [The observer-separation lattice](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/observer-lattice.md), §4's identity-fixing branch.

The theorem does not establish unrestricted reflection of existential assertions. Without (10), current $`\forall X\exists Y\,\varphi(X,Y)`$ does not give a witness whose E-image has the required property. Inextensible Comprehension alone is not covered: I(Y) is fixed, but it has not been shown to force pointwise-fixed Y. Nor are Weak Rigid or Weakly Inextensible Comprehension silently identified with their fully boxed qualifications. Any further arrows require separate arguments.

## 6. Sources

Definitions of persistence, inextensibility and rigidity: Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.3, pp. 28–30, as recorded in [Background](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/background.md) and the [Rigid Comprehension record](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/principles/rigid-comprehension-r.yaml). Persistent Comprehension and the Gallin comparison have locators p. 29, n. 38 and p. 28, n. 37 respectively.

The native definition □p:=(p=Top), NI, CBF, normal modal reasoning and Intensionality are the fixed framework facts in *Classicism*, §§1.3–1.5 and §2.1, pp. 13–22. The exact current ND_t premise is the [propositional ND record](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/principles/distinctness-necessary-t.yaml), source Proposition 2.2, p. 22. C5 is still the distinct, stronger schema □ND.

The finite-list observer mechanism follows the [ordinary qualification](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1. The existing [Boolean-completeness reflection proof](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/finite-colour-propositional-completeness.md), §5, is a related antecedent; the [native-Box universal reflection theorem](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/native-box-reflection.md), §§1–2, makes the unrestricted existential-witness obstacle explicit. The present proof resolves that obstacle for fixed witnesses.

