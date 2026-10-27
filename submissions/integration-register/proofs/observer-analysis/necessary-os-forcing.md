# Necessary observer separation: the projective fragment and the forcing boundary

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source: `misc`, this note, §§1–4, unpaginated. This note records a new argument in the present research without asserting historical novelty. No native records or formal-verification statuses are changed.

**Result and limit.** In the internally full Boolean-valued forcing models used in [the generic-point construction](os-analysis-model.md), necessary observer separation decides every projective $`\Sigma^1_3`$ and $`\Pi^1_3`$ sentence with ground-model real parameters. The [independent model audit](necessary-os-model-audit.md) already proves the stronger set-theoretic persistence criterion needed for this conclusion and separately derives noncontingency of CH. Neither note establishes the corresponding result in arbitrary Henkin models of C5 + □OS. The [two-Hechler construction](necessary-os-analysis-countermodel.md) gives a Σ¹₄ counterexample.

## 1. Exact semantic premise

Work internally to a model M of ZFC with a complete Boolean algebra B. Admit all M-coded functions at the relational types, interpret quantifiers by internal Boolean meets and joins, and interpret identity crisply. When a designated ordinary truth evaluation is needed, take M countable and choose an external M-generic ultrafilter. M need not be externally well founded: the statements below are proved in ZFC and then interpreted internally, for each fixed standard finite formula.

Let $`S=S_{t,\{t\}}`$ be the single propositional ordinary observer-separation instance whose qualification includes the universal quantifier at type t. In this model family, a qualified observer is exactly an internal complete unital Boolean endomorphism of B. Write $`\mathcal E`$ for their internal set. The exact value is

```math
\|S\|=\bigwedge_{0<b\in B}\bigvee_{h\in\mathcal E}h(b).
\tag{1}
```

Native necessity tests equality with the top Boolean value. Thus □S entails

```math
\bigvee_{h\in\mathcal E}h(b)=1_B\qquad(0<b\in B).
\tag{2}
```

For details establishing qualification, fullness and (1), see [the independent audit](necessary-os-model-audit.md), §§1–2. Full □OS supplies this single required premise; no extra observer qualification is being assumed.

The useful consequence of (2) is elementary. If $`h(b)\le b`$ for every $`h\in\mathcal E`$, then b is zero or one: for nonzero b, (2) yields $`1_B\le b`$.

## 2. Projective truth through level three

Fix a ground real a and a projective $`\Sigma^1_3(a)`$ sentence

```math
\varphi(a)\equiv\exists x\in\mathbb R\;\theta(x,a),
\qquad\theta\in\Pi^1_2.
\tag{3}
```

The standard forcing form of Shoenfield absoluteness says that a $`\Pi^1_2`$ statement with an existing real parameter is absolute between a model of ZFC and a set-forcing extension. A proof is given in Arnold W. Miller, [*Descriptive Set Theory and Forcing*](https://people.math.wisc.edu/~awmille1/res/dstfor.pdf), Theorem 20.2, printed p. 87. Applying it to $`\theta(x,a)`$, a witness x to (3) continues to witness (3) after further forcing. Thus each fixed $`\Sigma^1_3`$ formula is provably persistent under further set forcing.

Put $`b=\|\varphi(\check a)\|_B`$. For every internal complete endomorphism h,

```math
h(b)\le b.
\tag{4}
```

Here is the reason, including noninjective observers. The kernel of h is the principal ideal below

```math
k=\bigvee\{d\in B:h(d)=0\}.
```

Consequently h restricts to a complete unital embedding $`B\upharpoonright\neg k\to B`$. Pulling a B-generic ultrafilter back along this embedding gives an intermediate forcing extension of M; the full B-extension is a further quotient-forcing extension of it. Ground a is unchanged. If the intermediate extension satisfies (3), its witness x and Shoenfield absoluteness make the larger extension satisfy (3). The Boolean translation is exactly (4). This is the persistence lemma of [the independent audit](necessary-os-model-audit.md), §3, specialized to (3); its internal proof avoids imposing external transitivity on M.

Equations (2) and (4) prove

```math
\boxed{\Box S\ \Longrightarrow
\|\varphi(\check a)\|_B\in\{0_B,1_B\}
\quad(\varphi\in\Sigma^1_3).}
\tag{5}
```

Taking Boolean complements proves the same conclusion for $`\Pi^1_3`$. Lower projective levels are included. Without □S, the orbit calculation only gives $`\|S\|\le b`$ when b is nonzero and persistent; this does not force b to be an endpoint.

The parameter qualification matters. Equation (5) concerns sentences, or ground real parameters represented by their check names. It is not a claim that every formula with an arbitrary moving real name has an endpoint value. Likewise its translation to native analysis uses the restricted extensional forcing interpretation established in [the generic-point construction](os-analysis-model.md), §6; arbitrary intensional predicates are outside that transfer.

In particular, the existing witness “there is a nonconstructible real” is covered: membership in L is $`\Sigma^1_2`$, so its negation is $`\Pi^1_2`$, and existentially quantifying the real gives a $`\Sigma^1_3`$ sentence. The direct persistence argument is even shorter: set forcing preserves L and cannot make an already nonconstructible real constructible.

## 3. Why mutual complete embeddings do not settle necessary OS

The requirement is the covering condition (2), for every nonzero Boolean element and every target condition. Mutual complete embeddings alone do not imply this condition.

Joel David Hamkins gives an instructive example in his [answer to “When are two forcing posets the same?”](https://mathoverflow.net/questions/451494/when-are-two-forcing-posets-the-same/451505): two lottery sums mutually completely embed while one forces CH and the other forces its negation. His displayed forcings are

```math
P=\bigoplus_{n>1}\mathrm{Coll}(\omega,\beth_n)
 *\mathrm{Add}(\check\beth_n^{+},1),
\qquad
Q=\bigoplus_{n>1}\mathrm{Coll}(\omega,\beth_n)
 *\mathrm{Add}(\omega,\check\beth_n^{++}).
\tag{6}
```

The embeddings use sufficiently later summands. These are global mutual complete embeddings, not merely mutual embeddings of some intervals. The lotteries are not weakly homogeneous and their different summands collapse different ground ordinals. A statement that a fixed ground ordinal is countable can consequently have a nonzero, nonunit Boolean value. That statement is forcing-persistent, so (2) fails by the persistence lemma. Thus these examples do not furnish necessary-OS countermodels. The obstruction is the varying collapse information, rather than any general prohibition on mutually embedding nonisomorphic complete Boolean algebras.

More generally, the independent audit, §4, proves that (2) decides the forced cardinal status of every ground ordinal, hence fixes the ordinals that become $`\omega_1`$ and $`\omega_2`$. Once $`\delta`$ is the fixed forced $`\omega_2`$, the assertion of an injection $`\check\delta\to\mathcal P(\check\omega)`$ is persistent and is equivalent to ¬CH. Therefore CH is an endpoint throughout this construction class. Opposite-CH homogeneous factors cannot evade the same argument by mutually embedding.

The positive projective bound is sharp: the [two-Hechler model](necessary-os-analysis-countermodel.md) makes a Σ¹₄ assertion contingent. The CH conclusion here is restricted to internally full Boolean-valued forcing models; the [finite-support symmetric construction](necessary-os-ch-inaccessible-countermodel.md) gives a different Henkin model with contingent CH.
