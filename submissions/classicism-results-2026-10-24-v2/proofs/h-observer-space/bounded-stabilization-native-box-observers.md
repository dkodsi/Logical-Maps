# Stacked two-point antichains: an unbounded native-Box stabilization hierarchy

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated. The full action-model framework and the earlier coordinate-reader theorem are attributed in §7.

Requiring a native-Box observer to stabilize after a fixed number of iterations gives an unbounded strict hierarchy of separation principles. The first level is idempotent native-Box separation. Each larger bound gives a strictly weaker separation principle, and no fixed bound reduces to unrestricted native-Box separation. Finite full models witness every strict step, even with necessary ordinary logical separation, Barcan, Functionality, propositional Atomicity and .2. One infinite full model has necessary native-Box separation while failing every fixed finite stabilization bound.

The reason is structural. In a frame built from successive two-point antichains, a modal observer reading the first antichain must move each whole antichain bijectively to the next one. It cannot stabilize until it reaches the top. Explicit readers attain this forced bound.

## 1. Fixed finite bounds and theory scope

For a fixed external integer r≥1, define powers of an admitted observer E:tt by finite term iteration: E⁰=I and Eⁱ⁺¹=E∘Eⁱ. Use the full logical qualification $`\mathrm{Good}_\Delta`$ and native-Box identity from [Native-Box logical observers](native-box-logical-observers.md), §1. The additional stabilization condition is the whole operation identity

```math
 E^{r+1}=E^r
 \tag{1}
```

Write $`B_r(\tau,\Delta)`$ for separation by the common class satisfying $`\mathrm{Good}_\Delta`$, native-Box commutation and (1). Unindexed $`B_r`$ means the full schema over relational output types τ and finite external qualification lists Δ. A boxed $`B_r`$ means the separately boxed closed separation instances.

The index r is fixed in each principle. There is no object-language quantifier over natural numbers, no infinite qualification formula and no existential choice of an iteration bound inside $`B_r`$. In particular B₁ is exactly IdemBoxSep.

Multiplying (1) by E shows Eʳ⁺²=Eʳ⁺¹. Thus the qualifying classes grow with r, and their separation principles satisfy

```math
 B_1\ \Longrightarrow\ B_2\ \Longrightarrow\ B_3
 \ \Longrightarrow\ \cdots\ \Longrightarrow\mathrm{BoxSep}
 \tag{2}
```

These implications hold at each fixed τ,Δ, before any full-schema recovery argument. Full $`B_r`$ implies full BoxSep and hence recovers C, BF and Functionality over H. The model constructions below show that every successive arrow in (2) is strict, and that $`B_r`$⇒BoxSep is strict for every fixed r.

Over C5, every native-Box Boolean observer is injective. Finite repeated cancellation in Eʳ(Ep)=Eʳp therefore gives Ep=p for every p. Functionality collects E=I. The same argument as for idempotence then gives, for every fixed r≥1,

```math
\boxed{
\begin{aligned}
 \mathrm{C5}+B_r&\quad\Longleftrightarrow\quad\mathrm{Extensionality},\\
 \mathrm{Rev}+B_r&\quad\Longleftrightarrow\quad\mathrm{Extensionality},\\
 \mathrm{End}+B_r&\quad\Longleftrightarrow\quad\mathrm{Extensionality}
\end{aligned}}
\tag{3}
```

These are full-schema equivalences over H. With C5 already assumed, the forward collapse needs only propositional separation. Rev and End supply C5; their conjunctions with $`B_r`$ allow different separating observer families. Conversely Extensionality supplies all these principles through identity. No claim is made that the qualifying observer classes coincide without C5.

## 2. The full finite-frame interpretation

Use the construction and proof in [Idempotent native-Box observers](idempotent-native-box-observers.md), §§3–4. A finite rooted poset P is viewed as a thin category, with singleton individuals and full relational action-model domains. At a point x,
$`D_t(x)=\mathcal P(\mathord\uparrow x),`$
and current truth is membership of x. Relational objects are full future truth profiles. Transport restricts a profile to a future cone and is onto at every type, since every restricted profile extends by arbitrary values elsewhere. The construction therefore satisfies C, necessary BF, necessary Functionality and necessary propositional Atomicity.

Every Boolean observer is uniquely a coordinate reader E_f for an inflationary map f:P→P:

```math
 x\le f(x),\qquad E_f(p)=f^{-1}[p]
 \tag{4}
```

At an arbitrary future x, it reads an arbitrary input q⊆↑x at f(x). Every such map is admitted. Onto type transport proves its full composite preservation of all quantifiers, at every future input. Thus these readers are Good for every requested finite list. The translated equality clauses follow over C; no reflection of equality by individual transport arrows is required.

Native-Box preservation is exactly the cone-image condition

```math
 f[\mathord\uparrow x]=\mathord\uparrow f(x)
 \quad\text{for every }x
 \tag{5}
```

It entails monotonicity. The whole stabilization identity (1) is exactly

```math
 f^{r+1}=f^r
 \tag{6}
```

Both equivalences concern the entire observer: they are checked on every future input, with singleton propositions giving the converse direction for (6).

At the root o, qualifying observers separate propositions exactly when every a∈P occurs as f(o) for some qualifying f. If a is unread, ∅ and {a} agree under every qualifying observer. Conversely a read coordinate distinguishes any two different subsets. Functionality lifts this propositional separation to every relational output type. All success statements below therefore concern full types and all finite lists. The failures are already propositional at Δ={t}.

Every inflationary map on a finite poset of height h stabilizes by h iterations, where height counts the maximum number of strict steps in a chain and h≥1. Once an iterate fails to move strictly upward it is fixed; a strictly increasing orbit has at most h steps. Thus in each such full model, BoxSep and B_h coincide. There is no uniform h for all finite frames, as the following construction proves.

## 3. Exact first three levels on two antichains

For positive finite integers m,n, let $`P_{m,n}`$ have four levels: root o, an m-point antichain A, an n-point antichain B, and top 1. Every point in a lower level lies below every point in a higher level. In the full model,

```math
\boxed{
\begin{aligned}
 B_1&\quad\Longleftrightarrow\quad m=1\ \text{or}\ n=1,\\
 B_2&\quad\Longleftrightarrow\quad m=1\ \text{or}\ n=1\ \text{or}\ m>n,\\
 B_3&\quad\Longleftrightarrow\quad\mathrm{BoxSep}
 \quad\Longleftrightarrow\quad m=1\ \text{or}\ n\le m
\end{aligned}}
\tag{7}
```

The B₁ and BoxSep characterizations are proved in the idempotent note, §5, (7a). The former is the join-semilattice criterion. B₃ and BoxSep coincide by height three. It remains to prove the middle row.

Assume m,n≥2 and f satisfies (5) with f(o)=a∈A. The earlier coordinate proof shows that every point of B must map to top. Briefly, if b∈B were fixed, every x∈A other than a would have f(x)=b by monotonicity and inflationarity. Each other c∈B would then map to top, while f(a) could only be a or b. No input would map to c, contradicting f[P]=↑a.

Also f(a) cannot equal a. If it did, applying (5) at a would require f[↑a]=↑a, but its left side would be only {a,1}, omitting B. Thus f(a) is either an upper point or top. The B₂ identity evaluated at the root says f³(o)=f²(o). An upper value f(a) would move to top on the next step, so B₂ forces f(a)=1.

All n upper points must nevertheless occur in f[P]=↑a. Their only possible preimages now lie among the m−1 points of A other than a. Hence m>n.

Conversely, if m>n, fix any a∈A. Map the root to a, map a to top, map $`A\setminus\{a\}`$ onto B by an explicit finite surjection, and map B and top to top. At any x∈$`A\setminus\{a\}`$, its cone image is {f(x),1}=↑f(x); at a and at an upper point it is {1}; at the root it is ↑a. Thus (5) holds, and every orbit stabilizes in at most two steps. Each upper point b has a join with every point, so x↦x∨b gives an idempotent reader of b. Identity and the constant-top map read o and 1. These observers establish B₂.

If m=1 or n=1, the frame is a join-semilattice and already has B₁. This completes (7). Every proper future cone of $`P_{m,n}`$ is a join-semilattice, so each successful $`B_r`$ statement in (7) also holds necessarily.

In particular $`P_{3,2}`$ satisfies □B₂ but fails B₁. P_{2,2} satisfies □B₃ but fails B₂. The first frame has seven points and the second six. These are external descriptions of the models, not internal cardinality assumptions in their separation principles.

## 4. Arbitrarily long forced stabilization

For an external integer k≥2, define T_k to have a root o, k successive two-point antichains A₁,…,A_k, and a top 1. All cross-level order relations hold. Thus T_k has 2k+2 points.

**Theorem.** The full model on T_k satisfies □B_{k+1} but fails B_k at the root. More precisely, every native-Box reader f with f(o)=a∈A₁ must map A_i bijectively onto A_{i+1} for 1≤i<k, and must map A_k to top.

### The forced level maps

Fix such an f. Equation (5) at the root gives f[T_k]=↑a, so every point in A₂,…,A_k must have a preimage.

First suppose z∈A₂ were fixed. Let b be the other point of A₁. Monotonicity from the root and inflationarity give f(b)≥a,b, while b≤z gives f(b)≤z. Therefore f(b)=z. For the other point w∈A₂, monotonicity from b and inflationarity give f(w)≥z,w, so f(w) is strictly above A₂. Moreover f(a)≤z and f(a)≥a, so f(a) is either a or z. The root maps to a; points above A₂ cannot map down; and z is fixed. Hence w has no preimage, a contradiction.

Neither point of A₂ is therefore fixed. By inflationarity, a point of A₂ can only have a preimage at a lower level or at itself. The root does not read A₂, and neither point is its own preimage. Its preimages must lie in A₁. Both points of A₂ are read, so the two-point map A₁→A₂ is a bijection.

Now assume inductively that f maps each A_i bijectively onto A_{i+1} for i<j−1, where 3≤j≤k. Every point x∈A_{j−1} lies above all of A_{j−2}; monotonicity makes f(x) an upper bound of f[A_{j−2}]=A_{j−1}. It must therefore lie at level j or above.

If z∈A_j were fixed, x≤z would force f(x)≤z for every x∈A_{j−1}. Thus all of A_{j−1} would map to z. For the other w∈A_j, monotonicity from A_{j−1} gives f(w)≥z, and inflationarity gives f(w)≥w, so f(w) lies strictly above A_j. Earlier levels already map below A_j by the induction hypothesis; A_{j−1} maps only to z; later levels cannot map down. Consequently w would have no preimage. This is impossible.

Thus neither point of A_j is fixed, and its only possible preimages are in A_{j−1}. Both must be read, so f:A_{j−1}→A_j is a bijection. This proves the induction.

Finally, every x∈A_k lies above A_{k−1}. Its image is therefore an upper bound of f[A_{k−1}]=A_k. The only such point is top. Hence f[A_k]={1}.

In particular the root orbit visits one point of each level in order:

```math
 o\ \mapsto\ a\in A_1\ \mapsto\ A_2
 \ \mapsto\cdots\mapsto\ A_k\ \mapsto\ 1
 \tag{8}
```

Thus fᵏ(o)∈A_k but fᵏ⁺¹(o)=1. No B_k-qualified observer reads a. The distinct propositions ∅ and {a} consequently agree under every B_k observer, proving failure of B_k(t,{t}).

### Readers attaining the bound

For any a∈A_j, define f(o)=a and send every point in a level earlier than j to a. For each j≤i<k, map A_i bijectively onto A_{i+1}, choosing the two-element bijections explicitly. Send A_k and top to top.

At the root and at a point earlier than level j, the cone image is {a} together with every level strictly after A_j and top, exactly ↑a. At x∈A_i with j≤i<k, the image consists of f(x) together with all levels strictly above A_{i+1} and top, exactly ↑f(x). At level k and top, the cone image is {1}. Therefore (5) holds everywhere.

Every orbit stabilizes by k−j+2≤k+1 iterations. Identity reads the root and the constant-top map reads top. Thus every point is read by a B_{k+1} observer, establishing full B_{k+1} at the root.

A cone above a point of A_i is a smaller frame T_{k−i}, with that point as its singleton root. When there are at least two remaining antichains, the same construction applies with a smaller bound. With one or zero remaining antichains, the cone is a join-semilattice and has B₁; the top is the one-point case. Every cone therefore satisfies B_{k+1}, proving the separately boxed full schema. ∎

## 5. The strict hierarchy and its limits

The base case $`P_{3,2}`$ and the frames T_k together show, for every fixed external r≥1,

```math
\boxed{B_r\ \Longrightarrow\ B_{r+1}
\quad\text{strictly over H}}
\tag{9}
```

For r=1 use $`P_{3,2}`$. For r≥2 use T_r, which satisfies □$`B_{r+1}`$ but fails even the unboxed $`B_r`$. Thus the separately boxed hierarchy is also strict. The forward boxed implications follow by necessitating the unconditional class-inclusion theorem in C; the full boxed antecedent supplies the unboxed background through T and full separation.

All these witnesses have a common top in every future cone. Consequently .2 holds at every point: if some future cone is contained in p, then top belongs to p, and every future point can access that top. Therefore the entire hierarchy remains strict over the common background

```math
 \mathrm C+\Box\mathrm{BF}+\Box\mathrm{Functionality}
 +\Box\mathrm{OS}+\Box\mathrm{Atomicity}_t+\Box .2
 \tag{10}
```

For each r≥2, T_r also witnesses BoxSep without $`B_r`$. For r=1, T₂ does so. Hence no fixed stabilization bound gives all of BoxSep. These finite countermodels already prove the unbounded strict hierarchy. Section 6 supplies one infinite model violating every fixed bound at once. Neither conclusion identifies BoxSep with an infinitary disjunction of $`B_r`$ theories.

The four-point diamond already has B₁, and hence every $`B_r`$, while failing C5. In the opposite direction a terminal two-point cluster has End and Rev but fails Extensionality, so (3) makes it fail every $`B_r`$. Thus each fixed $`B_r`$ is incomparable with Rev and with End, even though conjoining either of those theories with $`B_r`$ gives Extensionality. The variable stabilization bounds refine the native-modal region without introducing a new reversible region under C5.

## 6. One infinite frame defeats every fixed bound

Let T_ω have a root o, successive two-point antichains A₁,A₂,…, and a common top 1. Every point in an earlier level lies below every point in a later level, and every nonterminal point lies below top. Use singleton individuals and the same full relational action-model construction. Restriction of full future profiles is still onto at every type, by extension outside the smaller cone. Hence C, necessary BF and necessary Functionality hold. Proposition domains are full powersets, giving necessary propositional Atomicity. The common top gives necessary .2 by the proof in §5.

The finite proof that every Boolean truth character reads a point no longer applies. The Q_t identity rules out the extra characters here. We give that admission and principality argument explicitly.

### The diagonal predicate

Fix any source x, and let E be $`\mathrm{Good}_{\{t\}}`$. Its current truth character is

```math
 h(q)=\text{the current truth value of }Eq,
 \qquad q\subseteq\mathord\uparrow x
 \tag{11}
```

Boolean qualification makes h a Boolean character. If it accepts a singleton {y}, then Boolean preservation makes h(q) true exactly when y∈q. Suppose instead that it accepts no singleton. Finite Boolean preservation then makes it reject every finite set and accept every cofinite set.

Define a full admitted predicate F:tt at x by the following future truth profile: for every y≥x and every q⊆↑y,

```math
 F(y,q)\text{ is true}\quad\Longleftrightarrow\quad q\ne\{y\}
 \tag{12}
```

Fullness admits this specified profile; no arbitrary-family encoding or external character-extension theorem is being assumed. For any current p⊆↑x, its application has profile

```math
 F_x(p)=\{y\ge x:p\cap\mathord\uparrow y\ne\{y\}\}
 \tag{13}
```

The omitted points are exactly the maximal elements of p in ↑x. They form an antichain, and every antichain of T_ω has at most two points. Thus F_x(p) is cofinite for every current p, including the cases where there are no maximal elements or only top is maximal. The assumed nonprincipal h therefore accepts every F_x(p).

But ∀p Fp is Bottom as a proposition: at each future y, choose the admitted input q={y}, which makes (12) false. Applying Q_t at x now yields a contradiction. Its left side h(∀p Fp)=h(Bottom) is false, while its right side ∀p h(F_x(p)) is true. Thus every $`\mathrm{Good}_{\{t\}}`$ truth character is principal.

Whole qualification applies the same argument at every future source. Consequently every $`\mathrm{Good}_{\{t\}}`$ observer on this frame is an admitted coordinate reader E_f for one inflationary map f, with the whole native-Box and finite-stabilization conditions still exactly (5) and (6). Conversely every inflationary coordinate reader is Good at every finite type list: the earlier arbitrary-future quantifier proof uses onto type transport, which holds in this infinite full construction as well.

The diagonal proof has a useful precise generality. In the full action model on any rooted poset of fixed finite external width, maximal elements of a subset form a finite antichain. The same admitted F therefore proves that every $`\mathrm{Good}_{\{t\}}`$ observer is a coordinate reader. Finite height is unnecessary. The cone-image characterization of native-Box preservation follows unchanged.

It also extends the earlier join theorem: **a full model on a rooted poset of finite external width satisfies full IdemBoxSep exactly when every pair of frame points has a join.** For necessity, a coordinate reader of a that is idempotent and satisfies (5) has image ↑a and fixes that image. Monotonicity and inflationarity then make f(x) the least upper bound of x and a, exactly as in the finite proof. For sufficiency, the admitted coordinate maps f_a(x)=x∨a satisfy (5) and are idempotent, and they read every point. Failure remains propositional at Δ={t}; success supplies all relational types and every finite list. This is a theorem about the specified full-model family, not a finite-width axiom added to the object language.

### Separation without a finite stabilization bound

For a∈A_j, send the root and every earlier level to a, map each A_i bijectively onto A_{i+1} for i≥j, and fix top. Its cone images are exactly ↑f(x), by the same calculation as in §4: the image at an earlier point is a together with all levels strictly above A_j and top. At a point in a later level, it is its image point together with every higher level and top. Identity reads the root, and the constant-top map reads top.

These maps read every point and give full BoxSep for every finite qualification list. Every nonterminal future cone has the same T_ω form after reindexing its levels; the terminal cone is a singleton. Thus the model satisfies □BoxSep.

Now fix a∈A₁. The forced-level induction in §4 applies at every finite stage: any native-Box coordinate reader f with f(o)=a must map A_i bijectively onto A_{i+1} for every finite i. Therefore fʳ(o)∈A_r and fʳ⁺¹(o)∈A_{r+1} for every fixed r≥1. It satisfies none of the finite stabilization identities.

Principality shows that this excludes every $`\mathrm{Good}_{\{t\}}`$ native-Box observer with a finite stabilization bound, not merely the explicitly constructed maps. For every fixed r, ∅ and the same singleton {a} agree under all $`B_r`$-qualified observers, although they are distinct propositions. Hence

```math
 \boxed{
 T_\omega\models\Box\mathrm{BoxSep},
 \qquad
 T_\omega\not\models B_r(t,\{t\})
 \quad\text{for every external finite }r\ge1}
 \tag{14}
```

The model retains the entire necessary background (10). Statement (14) is a metatheoretic family of verdicts about one fully specified model. It does not introduce an object-language natural-number quantifier, an infinite observer qualification, or an infinitary disjunction into the fixed framework.

## 7. Sources

The stabilization classification on $`P_{m,n}`$, forced-level theorem on T_k, strict hierarchy, infinite-frame separation and their comparisons are new ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated. The explicit coordinate maps, diagonal predicate and level induction above provide the evidence; no computational search or missing arrow is used as a nonimplication proof.

The full action-model construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). Its epic-transport Barcan criterion is Proposition 3.24(ii), recorded in [Full epic Barcan](../../source/topics/classicism/arguments/full-epic-barcan.yaml). The specialization to full finite rooted posets, all-type observer qualification and native-Box cone condition are proved in [Idempotent native-Box observers](idempotent-native-box-observers.md), §§3–5. The C5 injectivity equivalence is [Native-Box logical observers](native-box-logical-observers.md), §3. The earlier idempotent Extensionality and terminal-cluster comparisons retain the proofs and attribution in the idempotent note, §§2, 6–7.

Every theorem above retains a fixed external finite iteration bound and the fixed relational language.
