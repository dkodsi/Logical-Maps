# Reversible separation from conjunction-preserving involutions

Over C, full reversible logical separation is equivalent to one sentence about unary propositional operations. Its witnesses need only preserve conjunction and be their own inverses. All quantifier laws and separation at other relational types follow.

## 1. The sentence

Put $`I:=\lambda p^t\, .\,p`$ and define

```math
K(E):=\bigl((\lambda p,q\, .\,E(p\land q))=(\lambda p,q\, .\,Ep\land Eq)\bigr)
\land E\circ E=I.
```

The separation sentence is

```math
\forall X,Y^{tt}\, .\,
\bigl[\forall E^{tt}\, .\,K(E)\to\forall p^t\, .\,(E(Xp)\leftrightarrow E(Yp))\bigr]
\to X=Y.
```

**Theorem.** Over C, this sentence is equivalent to full Rev. Here Rev has its [existing full relational, finite-qualification-list definition](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md#1-definitions-and-scope).

The conjunction equation is an identity of whole operations. The separation type is $`tt`$, not just $`t`$. No quantifier-preservation clause or existentially supplied inverse occurs in $`K`$.

## 2. Recovering the background

**Functionality at tt.** If $`\forall p\, .\,Xp=Yp`$, substitution makes every eligible observer agree on their outputs. The displayed sentence gives $`X=Y`$.

**BF at t.** Let $`F^{tt}`$ be given and let $`b`$ be below every $`Fp`$ in the Boolean order. Functionality identifies $`F`$ with $`\lambda p\, .\,Fp\lor b`$. C's unconditional fixed-disjunct quantifier identity then gives

```math
\forall p\, .\,Fp
=\forall p\, .\,(Fp\lor b)
=\bigl(\forall p\, .\,Fp\bigr)\lor b.
```

Thus $`b\le\forall p\, .\,Fp`$. Taking $`b=\top`$ proves BF at t. This is the type-specific Functionality–Tractarianism–BF argument; no quantifier law for observers has been assumed.

**Propositional separation.** Apply the sentence to the two constant operations $`\lambda p\, .\,a`$ and $`\lambda p\, .\,b`$. Agreement under every eligible observer gives equality of the operations; application gives $`a=b`$.

**Boolean preservation.** Every eligible $`E`$ is bijective because $`E^2=I`$. Meet preservation makes it monotone and order-reflecting: if $`Ep\le Eq`$, then $`E(p\land q)=Ep`$, and applying $`E`$ gives $`p\land q=p`$. Consequently it is a Boolean order automorphism. The order characterizations of bounds, joins and complements give pointwise preservation of all Boolean operations. No all-type Functionality is needed at this stage.

**ND at t.** C identifies each H-valid equality-substitution formula with Top. Applying $`E`$ and using its pointwise Boolean preservation gives

```math
E(p=q)\to\bigl(E(Pp)\to E(Pq)\bigr).
```

Choose the admitted predicate $`P:=\lambda z\, .\,E(p=z)`$. Involutivity makes $`E(Pp)=(p=p)`$ and $`E(Pq)=(p=q)`$. Hence $`E(p=q)\to p=q`$; reflexivity and substitution give the converse. If $`p\ne q`$, every eligible observer therefore rejects both $`(p=q)`$ and Bottom. Propositional separation identifies them, yielding $`\Box(p\ne q)`$.

The established implications ND at t + BF at t ⇒ ☐ND at t ⇒ ☐ND at all types now give C5. All BF and Functionality instances are consequently available.

## 3. Recovering every quantifier law

Under BF, $`Q_\sigma(H):=\forall x^\sigma\, .\,Hx`$ is the greatest lower bound of the admitted range of $`H`$. Every admitted order automorphism preserves this bound. To see this directly, put

```math
m:=Q_\sigma(H),\qquad n:=Q_\sigma(E\circ H).
```

Monotonicity gives $`Em\le n`$. Choose $`b`$ with $`Eb=n`$, using surjectivity. Since $`Eb\le E(Hx)`$ for every $`x`$, order reflection gives $`b\le Hx`$, hence $`b\le m`$ and $`n\le Em`$. Therefore

```math
E(Q_\sigma(H))=Q_\sigma(E\circ H).
```

Functionality supplies the identity of the whole quantifier operations. Boolean identities likewise become whole-operation identities, and existential preservation follows by duality. The translated equality laws follow from Boolean preservation over C. Thus every eligible involution is a fully qualified reversible observer for every finite list.

Propositional separation, already recovered, now supplies each propositional Rev instance. Iterated Functionality lifts it to all relational types. This proves full Rev.

Conversely, full Rev supplies qualified involutive separators by the established [Boolean patching construction](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md#reversible-witnesses-can-be-involutions). Those separators satisfy $`K`$. If all $`K`$ observers agree on two tt operations at every input, the involutive separators do too, so the operations are identical.

## 4. The inverse-pair variant

The same equivalence holds if the involution equation is replaced by an admitted two-sided inverse:

```math
K'(E):=\bigl((\lambda p,q\, .\,E(p\land q))=(\lambda p,q\, .\,Ep\land Eq)\bigr)
\land\exists F^{tt}\, .\,E\circ F=I\land F\circ E=I.
```

The proof above uses $`F`$ in place of the second application of $`E`$, notably $`P(z):=F(p=z)`$ in the equality argument. The inverse is an order automorphism too, so its missing Boolean and quantifier laws follow. This converse follows directly from Rev's definition.

Both equivalences are over C. Replacing tt separation by proposition-only separation would remove the initial Functionality step and is not established by this argument. An external set-theoretic inverse cannot replace the admitted inverse.

## Sources

New characterization and bootstrap proof: OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026 (`misc`); source note *Observer routes through modal and maximalist principles*, §§E–F, unpaginated. The proof preserves the existing involutive-normalization dependency. Source hashes and the review receipt are in the [source manifest](../evidence/source-manifest.json) and [review evidence](../evidence/proof-reviews.json).

The Functionality, Tractarianism and BF equivalences are Bacon and Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.1 and n. 27, pp. 20–21. The ND bridges retain their [recorded proofs](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml).
