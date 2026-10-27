# Necessary observer separation blocks forcing variation of cardinal arithmetic

**Continuation update, 25 October:** this note's CH and persistence theorems stand. The [two-Hechler construction](necessary-os-analysis-countermodel.md) subsequently refuted general analytical propagation under C5 + □OS, within this very Boolean model class, with a nonpersistent Σ¹₄ sentence. It preserves CH and does not contradict the results below.

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated. This is a new argument in the present research, without a historical-novelty claim. It changes no native record or formal-verification status.

**Result and limit.** In the internally full Boolean-valued forcing construction, the single premise $`\Box S_{t,\{t\}}`$ forces every set-theoretic statement that is provably persistent under further forcing, with ground-model parameters, to have Boolean value zero or one. Consequently CH is decided throughout this construction, and so is the previously used analytical assertion that a nonconstructible real exists. Existence of a real structure at each admitted carrier type is also decided; therefore both universal CH assertions propagate literally, without an extra nonvacuity premise. This rules out the proposed two-factor and lottery-forcing countermodels to necessary OS. It is **not** a proof that arbitrary Henkin models of C5 + □OS have noncontingent CH or analysis.

## 1. Exact model family and separation premise

Work internally in a model M of ZFC with a nontrivial complete Boolean algebra B. Form the full admitted relational hierarchy in M, with proposition domain B, all M-functions at arrow types, Boolean meets and joins for quantifiers, and crisp identity. Externalize its standard finite types. If an ordinary designated truth evaluation is required, take M countable and evaluate at an M-generic ultrafilter on B.

The [generic-point audit](os-analysis-positive.md), §§1–3, verifies ordinary quantifier truth, lambda admission, native Leibniz identity and C5. Its arguments apply to an arbitrary B, not only to its displayed product $`2\times A`$. No external completeness of the countable externalized algebra is assumed. Below, every family, join, function and forcing calculation is internal to M. All arguments can first be proved in ZFC and then interpreted in M, so an externally well-founded M is unnecessary.

Use exactly the [whole-operation qualification](../../../classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1, and put

```math
S:=S_{t,\{t\}}=
\forall p,q^t\left[p=q\leftrightarrow
\forall E^{tt}\bigl(\mathrm{Good}_{\{t\}}(E)
\to(Ep\leftrightarrow Eq)\bigr)\right]
\tag{1}
```

Only this single closed formula is used. Necessary full OS supplies □S. Native Box is the global top test, so □S is true at any designated generic point exactly when the Boolean value of S is $`1_B`$.

## 2. Qualified observers are precisely internal complete homomorphisms

In this model, the admitted E satisfying $`\mathrm{Good}_{\{t\}}`$ are exactly the M-coded complete Boolean homomorphisms $`B\to B`$.

The forward implication has a useful fullness check. The whole Boolean identities make E a Boolean homomorphism fixing zero and one. Given any M-subset $`X\subseteq B`$, fullness admits

```math
F_X(b)=\begin{cases}b,&b\in X,\\1_B,&b\notin X\end{cases}
```

The whole universal-quantifier identity at type t gives

```math
E\!\left(\bigwedge X\right)
=E\!\left(\bigwedge_{b\in B}F_X(b)\right)
=\bigwedge_{b\in B}E(F_X(b))
=\bigwedge_{x\in X}E(x)
\tag{2}
```

Thus E preserves every internally indexed meet; complements give all joins. Conversely, an internal complete homomorphism preserves the coded range of every admitted predicate at every type. It therefore satisfies all whole Boolean and quantifier identities for every finite qualification list. Crisp equality and endpoint fixing give the remaining equality clauses.

Qualification itself has Boolean value zero or one. A failed whole-operation identity has value zero; when all those identities hold, the equality clauses have value one. There is no extra population of partially qualified observers that must be counted in (1).

Write $`\mathcal E=\mathrm{End}_{\mathrm{comp}}^M(B)`$, an M-set. For $`p\ne q`$, let $`r=p\mathbin{\triangle}q`$. Boolean preservation gives

```math
\left\|p=q\leftrightarrow
\forall E(\mathrm{Good}(E)\to(Ep\leftrightarrow Eq))\right\|
=\bigvee_{E\in\mathcal E}E(r)
```

The value is one when $`p=q`$. Since every nonzero r occurs as the difference of r and zero,

```math
\boxed{\|S\|=\bigwedge_{0<r\in B}\ \bigvee_{E\in\mathcal E}E(r)}
\tag{3}
```

Hence □S entails the full orbit-cover condition

```math
\bigvee_{E\in\mathcal E}E(r)=1_B\qquad(0<r\in B)
\tag{4}
```

Local complete embeddings alone do not establish (4): their direction, support and ability to cover each target condition matter.

## 3. Forcing-persistent truth values can only move downward

Call a set-theoretic formula $`\psi(\vec a)`$, with ground parameters $`\vec a`$, *forcing-persistent* here if ZFC proves that its truth in a forcing extension remains true after any further set forcing. Put

```math
p=\|\psi(\check{\vec a})\|_B
```

**Lemma.** Every $`E\in\mathcal E`$ satisfies $`E(p)\le p`$.

To include noninjective observers, set

```math
k=\bigvee\{b\in B:E(b)=0\},\qquad s=\neg k
```

Completeness gives $`E(k)=0`$, and $`E(s)=1`$. Also $`E(b)=0`$ exactly when $`b\le k`$. Therefore the restriction

```math
j=E\upharpoonright(B\upharpoonright s):
B\upharpoonright s\longrightarrow B
\tag{5}
```

is a unital injective complete Boolean homomorphism. Moreover $`E(b)=j(b\land s)`$ for every b.

Apply the complete-embedding forcing factor theorem to j. If H is B-generic, its inverse image under j is $`(B\upharpoonright s)`$-generic G; translated names give $`M[G]\subseteq M[H]`$, and the quotient forcing makes the latter a further forcing extension of the former. Ground parameters are unchanged. The Boolean value of $`\psi`$ for $`B\upharpoonright s`$ is $`p\land s`$. Thus, whenever $`E(p)=j(p\land s)`$ belongs to H, $`M[G]`$ satisfies $`\psi`$; persistence gives $`M[H]\models\psi`$, so $`p\in H`$. Equivalently $`E(p)\le p`$.

This is a ZFC proof about complete homomorphisms and forcing, and is interpreted internally when M is externally ill founded. It does not assume an external forcing theorem for nonstandard formulas. For the existence-of-function applications below, the persistence step simply retains the same witness function; its domain, range and injectivity conditions are bounded and remain true.

Combining the lemma with (4), if $`p\ne0`$, then

```math
1_B=\bigvee_{E\in\mathcal E}E(p)\le p
```

We obtain the main obstruction:

```math
\boxed{\Box S\quad\Longrightarrow\quad
\|\psi(\check{\vec a})\|_B\in\{0_B,1_B\}
\quad\text{for every such forcing-persistent }\psi}
\tag{6}
```

Without the box, (3) yields only $`\|S\|\le p`$ when $`p\ne0`$ is persistent. Current OS therefore makes a possibly true persistent assertion currently true; it does not make its Boolean value one. This explains why the earlier generic-point construction can satisfy current OS while changing CH or constructibility.

## 4. CH cannot vary in this family

For every ground ordinal $`\alpha`$, each of the following is forcing-persistent:

* “$`\check\alpha`$ is countable,” witnessed by an injection into $`\check\omega`$.
* “$`\check\alpha`$ is not a cardinal,” witnessed by an ordinal $`\beta<\check\alpha`$ and an injection $`\check\alpha\to\beta`$.
* For ground ordinals $`\kappa,\lambda`$, “there is an injection from $`\check\kappa`$ into $`\mathcal P(\check\lambda)`$.” Express its witness as a function on $`\check\kappa`$ whose values are distinct subsets of $`\check\lambda`$; adding subsets later does not invalidate it.

By (6), all these Boolean values are zero or one. The second assertion uses ZFC, where an ordinal is a cardinal precisely when it does not inject into a smaller ordinal.

There are a nonzero condition b and ground ordinals $`\gamma,\delta`$ such that

```math
b\Vdash\omega_1=\check\gamma\ \land\ \omega_2=\check\delta
\tag{7}
```

Indeed ordinal names can be decided on a dense set of conditions. Every ground ordinal below $`\gamma`$ is countable below b, and $`\gamma`$ is uncountable below b. Since those facts are individually decided by (6), they hold throughout B. Thus $`1_B\Vdash\omega_1=\check\gamma`$. Similarly $`\delta`$ is a cardinal throughout B, and every ordinal strictly between $`\gamma`$ and $`\delta`$ is not a cardinal throughout B. Consequently

```math
1_B\Vdash\omega_2=\check\delta
\tag{8}
```

The internal meets over those ordinal intervals are legitimate; no external countable-completeness assumption has entered the argument. In ZFC, with (8), CH is equivalent to the negation of

```math
\exists f\;[f:\check\delta\hookrightarrow\mathcal P(\check\omega)]
\tag{9}
```

The positive assertion (9) is forcing-persistent, so its Boolean value is an endpoint. Its negation therefore is too:

```math
\boxed{\Box S\quad\Longrightarrow\quad
\|\mathrm{CH}\|_B\in\{0_B,1_B\}}
\tag{10}
```

The same method fixes the relevant ground-ordinal cardinal comparisons and the cardinalities of the power sets of ground ordinals. The CH consequence already suffices to reject the proposed atomless product and lottery-forcing strategies. Mutual complete embeddings between homogeneous factors are unnecessary for this obstruction; arbitrary B is covered.

### Real-structure existence and literal propagation

Fix an admitted type $`\sigma`$, and write $`D=D_\sigma`$, an M-set. Choose a nonzero condition b and ground ordinals $`\kappa,\lambda`$ with

```math
b\Vdash |\check D|=\check\kappa\quad\land\quad
(\check\kappa)^+=\check\lambda
\tag{11}
```

The assertions that there are injections $`\check D\to\check\kappa`$ and $`\check\kappa\to\check D`$ are forcing-persistent, so (6) makes both globally true. Cardinal status of $`\kappa,\lambda`$ and every ordinal between them is already decided by (6). Therefore both assertions in (11) hold throughout B. This covers finite carriers too, using the ordinary next finite cardinal as successor.

By cardinal comparability in ZFC, the carrier-capacity assertion

```math
\mathrm{Cap}_D:=|\mathbb R|\le|\check D|
```

is consequently equivalent throughout B to the negation of
$`\exists f\,[f:\check\lambda\hookrightarrow\mathcal P(\check\omega)]`$.
The latter is forcing-persistent. Thus $`\|\mathrm{Cap}_D\|_B`$ is zero or one.

Use the restricted extensional forcing transfer in [the analysis construction](../dependencies/c5-functional-choice-analysis.md), §3, and put

```math
H_\sigma:=\exists\mathfrak R\,\mathrm{Real}_\sigma(\mathfrak R),
\qquad h_\sigma=\|H_\sigma\|_B
```

Every admitted tuple satisfying `Real` below a condition represents an internally complete ordered field on a subset of $`\check D`$. Its isomorphism with the extension's real field gives an injection $`\mathbb R\to\check D`$ below that condition. Hence $`h_\sigma\le\|\mathrm{Cap}_D\|_B`$.

If capacity has value one, M's Boolean maximum principle supplies a name for an injection $`j:\mathbb R\to\check D`$. Choose two distinct ground labels $`d_0,d_1\in D`$; capacity one ensures that they exist. A named finite permutation of $`\check D`$ adjusts j so that $`j(0)=\check d_0`$ and $`j(1)=\check d_1`$. Pull back the real-field carrier, order, ternary operation graphs and natural-numbers predicate along j. Each relation name on a finite power of $`\check D`$ normalizes to an M-function $`D^n\to B`$, and its curried form belongs to the full admitted relation domain. The fixed constants are the ground labels $`d_0,d_1`$. The extensional transfer makes this single admitted tuple satisfy `Real` with value one. No names for new individual constants or unavailable individual-valued operations are inserted into a type domain.

We have proved

```math
\boxed{h_\sigma=\|\mathrm{Cap}_D\|_B\in\{0_B,1_B\}}
\tag{12}
```

Let $`\chi=\|\mathrm{CH}\|_B`$, also an endpoint by (10), and use the exact universal formulations $`U_{\sigma,\mathrm{CH}}`$ and $`U_{\sigma,\neg\mathrm{CH}}`$. If $`h_\sigma=0`$, both universals have value one. If $`h_\sigma=1`$, categoricity gives the lower bounds $`\chi,\neg\chi`$; the single value-one real tuple just constructed gives the reverse bounds. Thus

```math
\|U_{\sigma,\mathrm{CH}}\|_B=\neg h_\sigma\lor\chi,
\qquad
\|U_{\sigma,\neg\mathrm{CH}}\|_B=\neg h_\sigma\lor\neg\chi
\tag{13}
```

Both values are endpoints. Therefore this model family validates the literal propagation implications for **each** universal CH side, as well as the native CH noncontingency disjunction. No actual-real-existence assumption or unproved mixing claim remains in that conclusion.

## 5. What this says about analysis

The already-used statement “there exists a nonconstructible real” is forcing-persistent. An existing real remains a real, and set forcing preserves ordinals and the constructible universe, so a real outside L cannot enter L after further forcing. Its Boolean value is therefore an endpoint under □S. The opposite sentence, “every real is constructible,” is decided as well.

The finite first-order analytical coding of this assertion is supplied by [the earlier analysis proof](../dependencies/c5-functional-choice-analysis.md), §4. The same extensional transfer therefore rules out this particular witness to native Necessity of Analysis in the present model family. Since (12) also decides real-structure existence, the argument of (13) proves literal propagation for each universal side of this particular analytical assertion as well.

No claim has been proved here for every projective sentence or every first-order sentence of the real field with its natural-numbers predicate. A candidate analytical counterexample would have to avoid the persistence obstruction for both its positive and negative forms, or leave this internally full Boolean-forcing construction.

## 6. Research boundary

The proof uses two features that cannot be silently assigned to an arbitrary Henkin model of C5:

1. Internal fullness admits every $`F_X`$ in (2), turning qualification at t into preservation of every internally coded Boolean meet.
2. The complete homomorphism then has the forcing interpretation (5), and the mathematical assertions have the restricted full extensional forcing interpretation used in §4.

Accordingly, the general questions for **C5 + □OS** remain outside this note's conclusion. What is settled is a substantial construction obstruction: no internally full Boolean-valued forcing hierarchy with necessary ordinary separation can make CH contingent, and its existing nonconstructible-real witness cannot make analysis contingent either.

No Lean, compilation, native-record edits or additional language extension was used.
