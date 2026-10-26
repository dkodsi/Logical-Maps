# Observer separation with one varying type

Over C, full OS is equivalent to propositional separation by Boolean observers preserving quantification at $`e`$ and at one varying relational type $`\rho`$. The proof compresses any finite list of relational types into a common retract type.

## 1. The shorter schema

Write $`Q_\sigma(F)=\forall x^\sigma\, .\,Fx`$ and $`E^*_\sigma(F)=\lambda x^\sigma\, .\,E(Fx)`$. Qualification at $`\sigma`$ is the whole-operation identity

```math
E\circ Q_\sigma=Q_\sigma\circ E^*_\sigma.
```

Let $`\mathrm{Bool}(E)`$ assert the Boolean preservation identities. For each relational type $`\rho`$, put

```math
K_\rho(E):=\mathrm{Bool}(E)
\land E\circ Q_e=Q_e\circ E^*_e
\land E\circ Q_\rho=Q_\rho\circ E^*_\rho.
```

The proposed presentation of OS is

```math
\forall p,q^t\, .\,
\bigl[\forall E^{tt}\, .\,K_\rho(E)\to(Ep\leftrightarrow Eq)\bigr]
\to p=q
\qquad(\rho\ne e).
```

The type parameter ranges externally over all relational types. This is a schema, not one finite sentence. Over C, existential preservation follows by duality and the translated equality clauses follow from Boolean qualification, as in the [existing observer definition](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md).

## 2. Preservation descends along definable retractions

Suppose closed H terms $`j:\sigma\rho`$ and $`r:\rho\sigma`$ satisfy $`r\circ j=I_\sigma`$ by conversion. The output $`\sigma`$ is relational. Define

```math
r^*(F):=\lambda z^\rho\, .\,F(rz).
```

H proves $`\forall z^\rho\, .\,F(rz)\leftrightarrow\forall a^\sigma\, .\,Fa`$: instantiate the left side at $`j(a)`$ for one direction and the right side at $`r(z)`$ for the other. C therefore gives the unconditional whole-operation identity $`Q_\sigma=Q_\rho\circ r^*`$. Conversion also gives $`r^*\circ E^*_\sigma=E^*_\rho\circ r^*`$. Consequently,

```math
\begin{aligned}
E\circ Q_\sigma
&=E\circ Q_\rho\circ r^*\\
&=Q_\rho\circ E^*_\rho\circ r^*\\
&=Q_\rho\circ r^*\circ E^*_\sigma\\
&=Q_\sigma\circ E^*_\sigma.
\end{aligned}
```

Thus preservation of $`Q_\rho`$ implies preservation of $`Q_\sigma`$. The only conditional step substitutes the assumed operation identity. The proof needs neither Boolean preservation nor BF, Functionality, Choice or optional necessitation.

## 3. A common retract for any finite relational list

For relational types $`\sigma_1,\ldots,\sigma_n`$, put

```math
\rho=(\sigma_1t)\cdots(\sigma_nt)t,
\qquad
j_i(a)=\lambda P_1\cdots P_n\, .\,P_i(a).
```

Write $`\sigma_i=\tau_1\cdots\tau_kt`$. Define $`r_i(z)`$ at an argument tuple by

```math
r_i(z)[\bar x]=z[K_1,\ldots,K_n],
\qquad
K_i=\lambda a^{\sigma_i}\, .\,a[\bar x],
\qquad
K_\ell=\lambda a^{\sigma_\ell}\, .\,\top\quad(\ell\ne i).
```

The tuple is empty if $`\sigma_i=t`$. Beta reduction gives $`r_i(j_i(a))[\bar x]=a[\bar x]`$; eta conversion gives $`r_i\circ j_i=I_{\sigma_i}`$ as an operation identity. All types are admitted because the outputs are relational.

The preceding lemma makes the same observer preserving $`Q_\rho`$ preserve every $`Q_{\sigma_i}`$. For an empty list take $`\rho=t`$. The individual type is treated separately: a retraction with output $`e`$ would not be a term of this language.

## 4. Equivalence to full OS

Full OS immediately supplies the schema in §1 by taking output $`t`$ and list $`\{e,\rho\}`$.

Conversely, the shorter schema first gives BF at every type $`\sigma`$. Choose $`\rho=\sigma`$ for relational $`\sigma`$, and $`\rho=t`$ for $`\sigma=e`$. If $`F(a)=\top`$ for every $`a`$, each qualifying observer sends every $`F(a)`$ to Top. Its quantifier law makes $`E(Q_\sigma(F))`$ true. Every such observer therefore agrees on $`Q_\sigma(F)`$ and Top, so separation identifies them. This is BF. The established BF equivalence supplies Functionality.

Now fix a finite qualification list $`\Delta`$. Use §3 to compress its relational members into one $`\rho`$. Every observer satisfying $`K_\rho`$ qualifies for $`\Delta`$, including $`e`$ when present. Hence the separating class from §1 gives propositional separation at $`\Delta`$. If two relations agree under all these tests at every argument tuple, propositional separation identifies their output propositions; repeated Functionality identifies the relations. This recovers full OS.

## 5. Why individual quantification cannot be omitted

Compare two existing full action models on the two-object chain $`0\to1`$. Model A has one individual at both objects. Model B has one individual $`a`$ initially and two individuals $`b,c`$ later, with $`a`$ transported to $`b`$.

Their complete typed reducts built from $`t`$ alone are identical. At $`t`$ both have

```math
D_t(0)=\{0,1\}^2,\qquad D_t(1)=\{0,1\},
\qquad q_t(p_0,p_1)=p_1.
```

At an arrow type, the full root domain consists of compatible profiles

```math
f_0:D_\sigma(0)\to D_\tau(0),\qquad
f_1:D_\sigma(1)\to D_\tau(1),\qquad
q_\tau\circ f_0=f_1\circ q_\sigma.
```

Transport sends the profile to $`f_1`$. Recursion through types built only from $`t`$ uses the same data in both models, including all logical operations and truth.

In Model A all type transports are onto. Inductively, a future function $`f_1`$ lifts to a compatible $`f_0`$ by selecting preimages along $`q_\tau`$; all domains here are finite. Since $`q_\sigma`$ is onto, the future function is determined by the root function, giving root Functionality.

Identity and the admitted terminal reader $`L(p_0,p_1)=(p_1,p_1)`$ separate propositions. Both preserve Boolean operations. Surjectivity of $`q_\sigma`$ makes quantifying over future objects equivalent to quantifying over the images of current objects, so $`L`$ preserves every $`Q_\sigma`$ as a whole operation. Functionality then gives full OS in A.

In Model B let $`H`$ be the haecceity of $`a`$: it holds of $`a`$ initially and of $`b`$ alone later. Every current individual necessarily satisfies $`H`$, but $`Q_e(H)=(1,0)`$ is not Top. Thus BF at $`e`$ fails, and so does OS.

It follows that no collection of entirely $`e`$-free sentences, even infinite, axiomatizes OS over C. Such sentences have identical truth values in A and B. Here $`e`$-free means that $`e`$ occurs nowhere in the types or expanded logical syntax, including the types of constants.

There is a stronger boundary. In B every relational transport is onto: the profile-lifting argument requires surjectivity of the output transport, starting at $`t`$, regardless of the input. Consequently $`L`$ preserves every relational quantifier, even at types involving $`e`$. Identity and $`L`$ separate at $`t`$ and $`tt`$, but

```math
L(Q_e(H))=(0,0),
\qquad
Q_e(\lambda x\, .\,L(Hx))=(1,0).
```

The only admitted Boolean observers are identity and $`L`$: their future component must be identity and their root truth coordinate one of the two Boolean characters. Only identity preserves $`Q_e`$, and it does not separate all propositions.

Thus neither propositional nor $`tt`$ separation qualified at all relational quantifiers can replace the $`e`$ requirement. This does not exclude stronger sufficient $`e`$-free conditions such as Rev.

## 6. Finite-basis boundary and sources

The [nonfinite-basis theorem](observer-no-finite-basis.md) shows that the unbounded type scope cannot be replaced by any finite equivalent collection of ordinary fixed-type sentences, even mentioning both $`e`$ and $`t`$. It also excludes equivalent axiom sets of uniformly bounded elaborated type order. The [C5 quantifier reduction](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/modal-selectors-and-quantifier-reduction.md) uses an additional assumption.

New common-retract construction, schema equivalence and model comparison: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`), §§1–5 above; source correspondence is in the [manifest](../evidence/source-manifest.json).

Model A is Bacon–Dorr's full two-object chain, *Classicism*, 16 May 2023 draft, §3.5, pp. 59, 61. Model B and its BF counterexample are Cian Dorr's construction of 11 October 2026. Their existing records are [the chain](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/full-two-object-chain.yaml) and [the chain with a new individual](https://github.com/zwlgzwlg/Logical-Maps/blob/a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb/logical-maps/topics/classicism/models/full-two-object-chain-new-individual.yaml). The new observer verdicts and reduct comparison are proved here.
