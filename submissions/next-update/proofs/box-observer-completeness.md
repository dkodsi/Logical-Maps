# Native-Box observers preserve propositional completeness through their images

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026. Source: `misc`, this proof, unpaginated.

Over C + BC_t, an idempotent logical observer commuting with native Box accepts BC_t. The same conclusion holds for a currently surjective logical observer commuting with native Box. Consequently, either corresponding separation principle makes current BC_t necessary. C5 and Actuality are not required.

## 1. Exact hypotheses

Let E:tt be admitted and Good_Δ for a finite external list Δ containing t and tt. Qualification uses identities between the whole Boolean and quantifier operations, as in [Logical observer separation](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1. Assume the additional whole-operation identity

```math
E\circ\Box=\Box\circ E
\tag{1}
```

Work over C + BC_t and assume either

```math
E\circ E=E
\tag{2a}
```

or current surjectivity

```math
\mathrm{Onto}(E):=\forall b^t\,\exists c^t\,[Ec=b]
\tag{2b}
```

Then E(BC_t) is currently true. Surjectivity in (2b) is not assumed necessary, and no admitted inverse or uniform choice of preimages is required.

Use the least-upper-bound form

```math
\mathrm{LUB}(c,Y):=
\forall q^t\left[
 \bigl(\forall p^t(Yp\to p\le q)\bigr)
 \leftrightarrow c\le q\right]
\tag{3}
```

Here p≤q abbreviates p∧q=p. Over C the proposition asserting this order equals Box(p→q). Thus (1) and Boolean preservation give the proposition-output identity

```math
E(p\le q)=(Ep\le Eq)
\tag{4}
```

It is (4), rather than acceptance of C5 alone, that identifies observed order with actual order between image elements.

## 2. Least bounds inside the image

Fix an arbitrary admitted Y:tt. Define the admitted predicate

```math
Z(z):=\exists p^t\,[E(Yp)\land Ep=z]
\tag{5}
```

Its current extension consists precisely of the E-images of the p for which E(Yp) is currently true. By current BC_t choose b with LUB(b,Z). This is a witness for the particular Y, not a function selecting joins for every predicate.

First suppose (2a). Each current Z-member z belongs to Im(E), so Ez=z. Since z≤b, monotonicity gives z≤Eb. Therefore Eb bounds Z. If an image element Eq bounds Z, leastness of b gives b≤Eq. Applying E and using (2a) gives Eb≤Eq. Hence Eb is the least upper bound of Z **within Im(E)**; it need not equal the ambient least upper bound b. In particular, for every q,

```math
\bigl[\forall p(E(Yp)\to Ep\le Eq)\bigr]
\leftrightarrow Eb\le Eq
\tag{6}
```

In the surjective case (2b), choose c with Ec=b. Ordinary leastness of b instead gives

```math
\bigl[\forall p(E(Yp)\to Ep\le Eq)\bigr]
\leftrightarrow Ec\le Eq
\tag{7}
```

In the idempotent case take c=b, so (6) is also (7). These are current truth assertions quantified over admitted objects. They have not been upgraded to identities by necessitating BC_t or a particular join witness.

## 3. Reflection into necessity

For the c just obtained, the Q_t and Boolean identities, together with (4), rewrite E(LUB(c,Y)) as

```math
\forall q\left[
 \bigl(\forall p(E(Yp)\to Ep\le Eq)\bigr)
 \leftrightarrow Ec\le Eq\right]
\tag{8}
```

Equation (7) makes this currently true. The P_t identity then makes E(∃c LUB(c,Y)) true. Since Y was arbitrary, the Q_tt identity gives

```math
E\bigl(\forall Y^{tt}\,\exists c^t\,
 \mathrm{LUB}(c,Y)\bigr),
\tag{9}
```

which is E(BC_t). The observer quantifier types used are exactly t for p,q,c and tt for Y. Formula (5) is admitted by ordinary lambda abstraction; it requires no further observer quantifier law.

Every eligible observer also sends Top to Top. Therefore either of the following single propositional separation instances, together with C + BC_t, gives BC_t=Top and hence native necessity of BC_t:

```math
\begin{aligned}
S_{t,\{t,tt\}}[\,E\circ\Box=\Box\circ E\ \land\ E^2=E\,]
&\quad\Longrightarrow\quad\Box BC_t,\\
S_{t,\{t,tt\}}[\,E\circ\Box=\Box\circ E\ \land\mathrm{Onto}(E)\,]
&\quad\Longrightarrow\quad\Box BC_t
\end{aligned}
\tag{10}
```

The background C + BC_t is retained in both lines. Larger finite qualification lists also suffice. Full typed separation is not needed for these implications. No optional premise was necessitated.

### Bounded stabilization

Fix an external integer r≥1. Let B_r be the observer restriction consisting of (1) and the whole identity E^(r+1)=E^r. Over C + BC_t,

```math
S_{t,\{t,tt\}}[B_r]\quad\Longrightarrow\quad
\Box\Diamond BC_t
\tag{10a}
```

Indeed E^r is an idempotent observer satisfying the same whole Boolean, listed quantifier and native-Box identities. The preceding theorem gives current truth of E^r(BC_t). Any whole Boolean observer F satisfies Fq≤Diamond q: F fixes Bottom necessarily, and equality congruence under q=Bottom gives Box¬q≤¬Fq. Apply this to F=E^(r−1), taking F=I when r=1, then apply the order-preserving E. This gives

```math
E^r q\le E(\Diamond q)
\tag{10b}
```

Thus every eligible E accepts Diamond BC_t. Separation identifies Diamond BC_t with Top, proving (10a). When r=1, (10) gives the stronger conclusion Box BC_t. For r≥2 no improvement to Box BC_t, and no strictness claim, is asserted here.

The same argument applies to any fixed external eventual-periodicity equation E^(m+n)=E^m with positive integers m,n: choose a positive multiple k of n with k≥m, so E^k is idempotent, and use (10b) with k. These are external finite parameters, not a quantification over natural numbers or an infinitary object-language disjunction.

## 4. General image condition and boundary

The proof also applies whenever, for each admitted Y, the current family

```math
\{Ep:E(Yp)\text{ is currently true}\}
\tag{11}
```

has a least upper bound within Im(E). Such a bound is an image element Ec, and (7) follows directly. Idempotence and current surjectivity are explicit sufficient conditions proved above. No completeness of the image of an arbitrary observer is asserted.

The [infinite-colour two-object countermodel](infinite-colour-conditional-completeness-countermodel.md) refutes C + OS + BC_t ⇒ Box(Box ND_t→BC_t); its single target satisfies full C5 and fails BC_t. An idempotent whole logical observer there accepts the boxed ND premise and rejects BC_t, but does not commute with native Box. Thus the positive native-Box theorem (10) remains unchanged. In particular E(p=q), the observed equality proposition, must not be replaced by actual equality Ep=Eq.

## 5. Sources and status

Definitions of whole qualification and separation are in [Logical observer separation](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1. The existing theorem under current C5, namely C5 + OS + BC_σ⇒Box BC_σ, is proved in [Finite colour patterns and propositional Boolean completeness](https://github.com/dkodsi/Logical-Maps/blob/52f324e09ca2df45d74ce4c522bcd761271efbed/submissions/classicism-results-2026-10-24-v2/proofs/h-observer-space/finite-colour-propositional-completeness.md), §5. The present proof adapts its logical transport step, using native-Box commutation and least bounds inside an observer's image in place of current C5's endpoint-valued equality judgments.

