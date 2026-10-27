# Two Hechler components: necessary observers with contingent analysis

Ordinary mathematical research by OpenAI Codex, 25 October 2026. The forcing inputs are Justin Palumbo, *Unbounded and dominating reals in Hechler extensions*, arXiv:1201.2932v1, Theorems 1–2, printed p. 2, and Proposition 5, printed p. 4. The Boolean product construction, necessary-observer argument and native analytical application below are new arguments in this research; their direct source is `misc`, this note, §§2–8, unpaginated. No historical-novelty claim or formal-verification claim is made.

**Result.** Relative to Con(ZFC), there is an internally full Boolean-valued relational Henkin model satisfying

```math
\mathrm{C5}+\Box\mathrm{OS}
  +\Box\mathrm{BF}_{\rm all}+\Box\mathrm{RelChoice}_{\rm all}
\tag{1}
```

in which a particular first-order sentence of $`(\mathbb R,+,\times,\mathbb N)`$ is contingent. The model has a real structure at carrier type t with Boolean value one. It refutes both the corresponding native noncontingency instance and literal propagation of its currently true universal side. Its proposition algebra is atomless. CH holds throughout this example; the CH obstruction proved in [the independent model audit](necessary-os-model-audit.md) remains intact.

## 1. Forcing inputs and their exact scope

Work in ZFC. Ordinary Hechler forcing $`\mathbb D`$ consists of pairs $`(s,f)`$, where $`s\in\omega^{<\omega}`$, $`f\in\omega^\omega`$. Stronger conditions extend the stem, increase f pointwise, and put new stem entries above the old bound. Tree Hechler forcing $`\mathbb T`$ consists of trees on $`\omega^{<\omega}`$ with a stem and cofinitely many successors at every node extending the stem, ordered by inclusion. Conditions sharing a stem are compatible in each forcing; hence both are $`\sigma`$-centered.

For a ground model V, say x is **unbounded over V** if no $`f\in V\cap\omega^\omega`$ eventually dominates x, and y is **dominating over V** if it eventually dominates every such f. The cited [Palumbo paper](https://arxiv.org/pdf/1201.2932) supplies exactly these inputs:

* Theorem 2, p. 2: $`\mathbb D`$ forces an unbounded x eventually dominated by every dominating y.
* Theorem 1, p. 2: $`\mathbb T`$ forces the negation of that assertion.
* Proposition 5, p. 4: each forcing adds a generic real for the other, by uniform ground-coded names.

The predicates in the first two inputs refer to the original ground model, not to a varying intermediate model. The third input will be used only to obtain complete unital Boolean homomorphisms. Injectivity, equivalence of the forcings, and an inverse pair of maps are unnecessary.

## 2. Both components are weakly homogeneous

Write

```math
A=\mathrm{RO}(\mathbb D),\qquad
C=\mathrm{RO}(\mathbb T).
```

All the following constructions can be performed within the ground model.

For $`\mathbb D`$, fix n. The conditions with stem length at least n form a dense suborder. Choose permutations $`\pi_i`$ of $`\omega`$, for $`i<n`$. On that suborder, replace the first n stem entries $`s(i)`$ by $`\pi_i(s(i))`$, leaving f and the remaining entries unchanged. This is an order automorphism: all entries added in a comparison of two such conditions have indices at least n, and every bound comparison is unchanged. It extends to an automorphism of A.

Given two conditions, first extend their stems to a common length n. Choose the $`\pi_i`$ to send the first extended stem to the second. The image of the first extended condition and the second then have the same stem; the pointwise maximum of their bounds is a common extension. Therefore for any nonzero $`a,b\in A`$, some automorphism $`\alpha`$ satisfies $`\alpha(a)\wedge b\ne0`$.

For $`\mathbb T`$, first extend two stems to a common length. A rooted-tree automorphism, using permutations of the successor sets at finitely many nodes, sends one stem to the other. It preserves cofinite successor sets, tree inclusion and the set of conditions. Two resulting trees with the same stem have a common extension given by their intersection above that stem. Thus C is weakly homogeneous as well.

For either algebra, weak homogeneity gives the exact consequence needed below:

```math
\bigvee_{\alpha\in\mathrm{Aut}(A)}\alpha(a)=1_A
\quad(a>0),
\qquad
\bigvee_{\beta\in\mathrm{Aut}(C)}\beta(c)=1_C
\quad(c>0).
\tag{2}
```

For example, a nonzero complement of the first join would contradict weak homogeneity applied to a and that complement. The automorphism sets and joins in (2) are internal sets and joins.

## 3. Generic names give the required cross-component maps

Palumbo's generic names yield complete unital Boolean homomorphisms

```math
j:A\longrightarrow C,
\qquad k:C\longrightarrow A.
\tag{3}
```

Here is the precise general fact being used. If forcing with a complete algebra C supplies a ground A-generic ultrafilter $`\dot H`$, put

```math
j(a)=\|\check a\in\dot H\|_C.
\tag{4}
```

Ultrafilter properties give the finite Boolean operations and endpoint preservation. For a ground family $`X\subseteq A`$, take a maximal antichain refining $`X\cup\{\neg\bigvee X\}`$. Genericity meets that antichain. It follows that membership of $`\bigvee X`$ in $`\dot H`$ is equivalent to membership of some member of X, so

```math
j(\bigvee X)=\bigvee_{a\in X}j(a).
```

Complements give arbitrary meets. This proves the completeness assertion, without silently identifying “adds a generic” with an injective embedding. Apply the argument in both directions to obtain (3).

## 4. The atomless product has necessary ordinary observer separation

Set

```math
B=A\times C.
```

This is the Boolean algebra for a two-way lottery between the two forcings, not their forcing product. Both factors, and hence B, are atomless. Besides the product automorphisms $`\alpha\times\beta`$, B has the complete unital endomorphism

```math
H(a,c)=(k(c),j(a)).
\tag{5}
```

We claim that every nonzero $`b\in B`$ has full endomorphism orbit:

```math
\bigvee_{h\in\mathrm{End}_{\rm comp}(B)}h(b)=1_B.
\tag{6}
```

Suppose first that $`b=(a,c)`$ with $`a>0`$. Product automorphisms applied to b have first-coordinate join one, by (2). Applying H after those automorphisms gives second-coordinate join at least

```math
\bigvee_{\alpha}j(\alpha(a))
 =j\!\left(\bigvee_{\alpha}\alpha(a)\right)
 =j(1_A)=1_C.
```

The join over the union of these two families is therefore $`(1_A,1_C)`$. If instead $`c>0`$, use C's automorphisms and k in exactly the same calculation, with the coordinates interchanged. This proves (6).

Form the internal full relational hierarchy with proposition domain B. A complete unital Boolean endomorphism is an admitted term of type tt and satisfies every finite list of the whole-operation observer identities: it preserves Boolean operations and every internally indexed quantifier meet or join. Native identities are crisp; their values are endpoints and are therefore preserved. Thus all the endomorphisms used in (6) are qualified observers at every finite qualification list.

For different propositions p and q, the difference $`b=p\mathbin{\triangle}q`$ is nonzero, and the Boolean value of their observer separation is the join in (6). Therefore the propositional separation formula has value one. For two different predicates of any admitted relational type, some argument tuple gives a nonzero difference. Applying the same calculation at that tuple makes the observer-separation formula have value one. Conversely identical predicates are of course indistinguishable. This proves every native OS instance with Boolean value one, hence

```math
\boxed{\Box\mathrm{OS}_{\rm all}.}
\tag{7}
```

The argument establishes ordinary observers. It does not assume that H has an inverse or that observers are reversible.

## 5. Externalization and the base logical theory

Take a countable model $`M\models\mathrm{ZFC}+V=L`$, and perform §§1–4 internally to M. Externalize its standard finite relational types. One may take $`D_e=\omega^M`$, $`D_t=B^M`$, and at every admitted arrow type all functions of that type belonging to M. Predicates are internally B-valued functions; quantifiers use the internal meets and joins.

Choose an external M-generic ultrafilter on B, concentrated on either desired component. The direct dense-family lemma of [the earlier full model](os-analysis-model.md), §§2–3, gives ordinary classical quantifier truth at this point: an internal join belongs to the generic ultrafilter exactly when one of its indexed entries does, and the dual statement holds for meets. Internal fullness admits lambda terms and the singleton characteristic predicates that make native Leibniz equality crisp. Native □ is the top-value test. The same verification gives C5.

Every construction and forcing fact used above is a ZFC theorem applied inside M. No external completeness of $`B^M`$, external transitivity of M, or forcing theorem for arbitrary nonstandard formulas is assumed. For each standard finite formula involved in the argument, M's internal proof and its internal Boolean interpretation suffice.

The earlier proofs of necessary BF and necessary Relational Choice also apply unchanged to this arbitrary internally complete B: BF commutes a meet with the crisp top test, and Relational Choice uses an internal well-order to disjointize each relation's rows. See [the earlier full model](os-analysis-model.md), §3. Together with (7), this establishes every premise in (1).

If ZFC is consistent, so is ZFC + V=L; completeness and downward Löwenheim–Skolem supply such a countable M. Its internal forcing algebra has an external M-generic ultrafilter. Thus the metatheory required for this construction is relative Con(ZFC), without a countable-transitive-model assumption.

## 6. A parameter-free analytical sentence distinguishing the components

In a forcing extension of M, its constructible universe is the original M, internally: set forcing preserves ordinals, and M satisfies V=L. Consequently reference to the original ground reals can be replaced by the parameter-free predicate “belongs to L.”

For $`x,y\in\omega^\omega`$, define

```math
\begin{aligned}
U_L(x)&\equiv
 \forall f\in\omega^\omega\,[f\in L\to x\not\le^*f],\\
D_L(y)&\equiv
 \forall f\in\omega^\omega\,[f\in L\to f\le^*y],\\
\varphi&\equiv
 \exists x\in\omega^\omega\left[
 U_L(x)\land
 \forall y\in\omega^\omega\,(D_L(y)\to x\le^*y)
 \right].
\end{aligned}
\tag{8}
```

This says that an unbounded function exists which lies eventually below every function dominating all constructible functions. The word “unbounded” prevents the assertion from being trivially witnessed by a small constructible function.

Membership of a real in L has a standard $`\Sigma^1_2`$ definition; see Veličković and Woodin, [*Complexity of the reals of inner models of set theory*](https://arxiv.org/pdf/math/9501203), Introduction, printed p. 1. Each of $`U_L`$ and $`D_L`$ is consequently $`\Pi^1_2`$: move the universal real f and the universal quantifiers in the negated membership predicate to the front. The universal y clause in (8) is $`\Pi^1_3`$, and φ has a $`\Sigma^1_4`$ presentation. In particular the previously established $`\Sigma^1_3/\Pi^1_3`$ obstruction does not cover this sentence.

By the cited forcing theorems, the exact Boolean values are

```math
\|\varphi\|_A=1_A,
\qquad \|\varphi\|_C=0_C,
\qquad \|\varphi\|_B=(1_A,0_C).
\tag{9}
```

There are no extra set-theoretic parameters in φ. The use of V=L occurred in choosing M and justifies its replacement of ground membership by constructibility.

For completeness, φ can be expressed by a finite first-order sentence in the real-field language with its natural-numbers predicate. Code a subset X of $`\omega`$ by $`r_X=\sum_{n\in X}4^{-(n+1)}`$, using base-four digits 0 and 1 and restricting coding reals to $`[0,1/3]`$. Digits are recovered from $`\lfloor4^{n+1}r_X\rfloor-4\lfloor4^nr_X\rfloor`$; the remaining tail is at most one third, so no endpoint carry interferes. The digit relation and the predicate restricting all digits to 0 or 1 are definable in $`(\mathbb R,+,\times,\mathbb N)`$, using integer quantifiers and arithmetically definable exponentiation. Coding subsets of $`\omega^2`$ by an arithmetical pairing function then codes the graphs of $`\omega`$-valued sequences. Totality, functionhood and eventual domination are arithmetical conditions on these codes. Replace each real/function quantifier in the projective formula by a first-order quantifier over its appropriate coding reals, with the coding predicate as guard. Ordinary number quantifiers are restricted using $`\mathbb N`$. The standard projective definition of constructibility is itself a finite second-order-arithmetic formula, so the same translation applies to it. This produces a particular finite sentence $`\varphi^\ast`$ of the required analytical language, equivalent to (8) in every internally complete real field with its natural-numbers predicate in the full model used here.

## 7. Real existence, capacity and the native contingency calculation

Internally to M, CH holds. Each forcing has size at most $`\omega_1`$, is ccc, and has at most $`(\omega_1)^\omega=\omega_1`$ nice names for reals. Both preserve $`\omega_1`$. They therefore force CH and a continuum of size $`\omega_1`$.

Each of A and C has size at most $`\omega_1`$: in a ccc completion every regular open is the join of a countable antichain from the underlying poset. Each also has size at least the ground continuum, since an atomless complete Boolean algebra contains a countably infinite antichain and the distinct joins of all its subsets. Thus

```math
|A|^M=|C|^M=|B|^M=\omega_1^M.
\tag{10}
```

The carrier t, whose underlying domain is the ground set B, has adequate size in both forcing components. Each component forces an injection of its real field into $`\check B`$, and the ground real field injects into B as well. By the Boolean maximum principle choose a name for this injection, and compose it with a named finite permutation so that zero and one have two fixed, distinct ground labels in B. Pulling back the carrier, natural numbers, order and field-operation graphs gives names for relations on finite powers of $`\check B`$. Normalize each such name as an M-function $`B^n\to B`$, and curry it into the admitted relational domain. Thus there are actual admitted constants and relation objects, rather than unadmitted names for individual-valued functions. The extensional forcing transfer of [the earlier model](os-analysis-model.md), §6, and [the capacity audit](necessary-os-model-audit.md), §4, supplies an admitted real structure $`R^\ast`$ at carrier t with

```math
\|\mathrm{Real}_t(R^\ast)\|_B=1_B.
\tag{11}
```

Here Real uses standard completeness for nonempty bounded subproperties, as explicitly chosen by the user. The full internal predicate domains represent every internal forcing name for a subset or finite-arity relation on this coded field. Complete ordered-field categoricity and the analytical coding in §6 apply on every Boolean support where a real structure exists.

Write the native universal sides as

```math
\begin{aligned}
U_\varphi&:=\forall R\,[\mathrm{Real}_t(R)\to\varphi^\ast(R)],\\
U_{\neg\varphi}&:=\forall R\,[\mathrm{Real}_t(R)\to\neg\varphi^\ast(R)].
\end{aligned}
```

Transfer and (9) give the lower bounds for all real structures. The total witness (11) supplies the matching upper bounds. Hence exactly

```math
\|U_\varphi\|_B=(1_A,0_C),
\qquad
\|U_{\neg\varphi}\|_B=(0_A,1_C).
\tag{12}
```

Both values are proper nonzero elements. Native □ tests the top element, so both $`\Box U_\varphi`$ and $`\Box U_{\neg\varphi}`$ have value zero. Their disjunction, the corresponding native Necessity of Analysis instance, fails everywhere in this model.

At a designated generic ultrafilter on A, $`U_\varphi`$ is currently true but $`\Box U_\varphi`$ is false. At one on C, the same holds for $`U_{\neg\varphi}`$. These are literal failures of truth-to-necessity propagation, with real existence guaranteed by (11), not vacuous universal truths.

CH, in contrast, has Boolean value one in both components. Accordingly this model separates necessary observer separation from Necessity of Analysis while respecting the full-Boolean CH obstruction.

## 8. What the countermodel establishes

Relative to Con(ZFC), C5 + □OS does not imply native Necessity of Analysis, even with necessary BF at every type and necessary Relational Choice at every admitted type pair. The separation uses an atomless proposition algebra and a finite analytical sentence with a $`\Sigma^1_4`$ presentation. It does not require an infinitary extension of the object language.

This resolves the higher-projective construction gap left in [the preceding forcing investigation](necessary-os-forcing.md), §4. It does not decide the general CH question outside the internally full Boolean model family. No compilation, Lean work or native-record edit was performed.
