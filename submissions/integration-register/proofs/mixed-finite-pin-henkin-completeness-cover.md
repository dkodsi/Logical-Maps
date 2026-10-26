# A complete observer source for mixed finite support and Henkin targets

Ordinary mathematical research by OpenAI Codex, 25 October 2026. Direct source: `misc`, §§1–7 below, unpaginated. This generalizes the [infinite-colour two-object construction](../../next-update/proofs/infinite-colour-conditional-completeness-countermodel.md). The inherited semantic frameworks are identified in §8. ## 1 Simultaneous preservation theorem

Work in ZFC. Take any nonempty set-sized family of the following components, made disjoint.

- **Finite-support components:** symmetric ideally-full action models with finite pinning sets at every object. The underlying category consists of nonempty sets and functions, with a designated group of automorphisms at each object. Individuals are the pinning carriers, or the component is a uniform singleton-individual variant.
- **Extensional Henkin components:** one-world extensional Henkin models of C in the fixed relational language. Their higher function domains may be proper Henkin domains. Their proposition domains are $`\{0,1\}`$.

The theorem is in the pure relational language; no simultaneous expansion preserving arbitrary fixed nonlogical constants is claimed. There is a single C model with a new source o satisfying


```math
OS+BC_t+BF_{\mathrm{all}}+\neg\mathrm{Actuality},
 \tag{1}
```


such that every original component, including all its typed domains, operations, arrows and truths, is unchanged and reachable from o.

Here OS is full typed logical separation for every finite qualification list, with the original whole-operation identities. No boxed BF or boxed OS at the source is asserted unless the chosen targets themselves satisfy those instances.

Consequently, any set of pure sentences which have witnesses among the permitted components can be made simultaneously possible at one source satisfying (1). Choose one component witness for each sentence and apply the construction once. In particular, one source can reach both the C5 target with $`\neg BC_t`$ from the preceding note and arbitrary extensional Henkin witnesses of arithmetic alternatives.

This is a simultaneous possibility theorem for the specified semantic classes. It is not Maximalism relative to C: arbitrary intensional Henkin components are not included.

## 2 The new category and source domains

Let $`\mathcal V`$ be the set of old objects. For an ordinary finite-support object V let $`A_V`$ be its auxiliary pinning carrier. For a one-world Henkin object M put $`A_M=D_e(M)`$. All these carriers are nonempty.

Choose a set K with at least two elements admitting a surjection $`\theta_V:K\to A_V`$ for each old object. For example, take the disjoint union of the carriers with two extra points, and send the other summands and extra points to a selected point of $`A_V`$. Define


```math
X=K\times\mathbb N,\qquad
 C_k=\{k\}\times\mathbb N,\qquad
 \beta(k,n)=k,\qquad
 \beta_V=\theta_V\beta .
 \tag{2}
```


Every fibre of every $`\beta_V`$ is infinite. Set


```math
\begin{aligned}
 \mathrm{End}(o)&=\mathrm{Sym}(X),\\
 \mathrm{Hom}(o,V)&=A_V^X,\qquad
 \mathrm{Hom}(V,o)=\varnothing,\\
 G_o&=\prod_{k\in K}\mathrm{Sym}(C_k).
\end{aligned}
 \tag{3}
```


All old arrows and groups remain unchanged. Composition with an old arrow is composition of auxiliary-carrier maps; composition with a source permutation is precomposition. For a Henkin target M the only old arrow is its identity. Thus (3) is a category.

Source individuals are X. Into a component whose individuals are its carrier, an arrow h acts on individuals as h. Into a singleton-individual component it acts by the unique map. These actions compose correctly with the old individual actions.

The source relational domains consist of symmetric finitely pinned profiles, with one additional landing requirement for Henkin targets. For $`\tau=\bar\sigma t`$, a profile has values


```math
A(h,\bar z)\in\{0,1\},
 \qquad h:o\to V,\quad
 \bar z\in\prod_i D_{\sigma_i}(V).
 \tag{4}
```


Finite pinning and symmetry have their usual meanings:


```math
\begin{aligned}
 h|_P=l|_P&\ \Longrightarrow\ A(h,\bar z)=A(l,\bar z)
       &&\text{for arrows with the same target},\\
 A(\mu h,\rho_\mu\bar z)&=A(h,\bar z)
       &&(\mu\in G_V).
\end{aligned}
 \tag{5}
```


At a Henkin target M, require the row $`A(h,-)`$ to be the actual extension of an entity in $`D_\tau(M)`$. Extensionality makes that entity unique. It is, by definition, the transport of A along h.

At an ordinary finite-support target V no extra restriction is necessary. If P pins A, then its transport along h is pinned by the finite set $`h[P]`$. Symmetry is inherited. The target is ideally full, so this transported profile is already an admitted entity.

Source transport and application use the standard rules


```math
(\rho_fA)(h,\bar z)=A(hf,\bar z),
 \qquad
 (A[\bar x])(h)=A(h,\rho_h\bar x).
 \tag{6}
```


These domains are defined recursively on types. The source is not required to be ideally full at higher types when Henkin targets are present.

**Closure under the language.** If the parameters of a term have finite pins with union P, their full transports along h depend only on $`h|_P`$: after every subsequent old arrow k, the composites kh and kl still agree on P whenever h and l do. Thus the term's profile is P-pinned. Target symmetry is preserved by the logical operations.

Landing in an ordinary target follows from finite pinning and ideal fullness. Landing in a Henkin target follows from that target's own lambda comprehension: the transported parameters are admitted M entities, and the row is the denotation in M of the same term with those parameters. In particular, no arbitrary external higher function is inserted into an M domain. Application and currying are covered by the same argument.

The action-model proof of C therefore applies. Every old component is unchanged because no arrow leads from it back to o.

## 3 The selected arrows have onto actions at all types

Every source permutation acts bijectively at all types. For any old object V, an arbitrary map $`h:X\to A_V`$, and any finite $`P\subseteq X`$, define b to agree with h on P and with $`\beta_V`$ outside P. Then


```math
b|_P=h|_P,\qquad b\text{ is surjective}.
 \tag{7}
```


Indeed finite modification cannot empty any infinite fibre of $`\beta_V`$. Such b will be called a selected arrow.

At individual type, a selected arrow is onto by (7), or by the singleton convention. There are two relational lifting arguments.

**Ordinary finite-support target.** Let $`A\in D_\tau(V)`$ have finite pin T. Choose a finite section $`s:T\to X`$ of b, so $`bs=1_T`$. Define a source lift $`\widetilde A`$ to have zero self rows. For an old-target arrow $`l:o\to W`$, put


```math
\widetilde A(l,\bar z)=
 \begin{cases}
 A(k,\bar z),&
 \text{if some old }k:V\to W\text{ satisfies }k|_T=ls,\\
 0,&\text{if no such }k\text{ exists}.
 \end{cases}
 \tag{8}
```


If two k work, they agree on T, so the row is well-defined. The profile is pinned by $`s[T]`$. For target symmetry, $`\mu\in G_W`$ sends a matching k to the matching $`\mu k`$; the inverse $`\mu^{-1}`$ gives the converse existence implication, and symmetry of A gives covariance of the row. At Henkin targets outside V's component there is no matching old arrow, so the row is zero and satisfies their landing requirement.

For every old $`k:V\to W`$ and arbitrary target tuple,


```math
(\rho_b\widetilde A)(k,\bar z)
 =\widetilde A(kb,\bar z)
 =A(k,\bar z),
 \tag{9}
```


since $`(kb)s=k|_T`$. This is equality of full future profiles, with arbitrary future arguments. It proves onto transport at every relational type, even when some old arrows k are not onto.

**One-world Henkin target.** For $`A\in D_\tau(M)`$, use its actual table as the row at every M-target arrow, and zero at every other target and at source self-arrows. This is empty-pinned, symmetric, and satisfies all landing conditions. Its transport along any arrow o→M is exactly A. Thus relational transport is onto; individual transport is onto for the selected arrows.

The argument requires neither fullness of the Henkin higher domains nor an external function-space completion of them.

## 4 Source completeness from orbit envelopes

Let $`B=D_t(o)`$. For finite P, let $`B_P`$ be the P-pinned proposition subalgebra. The Henkin row restriction does not reduce $`B_P`$, because every bit is an admitted proposition at an extensional target.

On a source self-arrow, a symmetric P-pinned proposition depends exactly on the colour pattern $`\beta h|_P\in K^P`$. Every finite colour pattern is realized by a permutation of X, using distinct points in each indicated infinite colour class.

On an ordinary old target V it depends exactly on the orbit of $`h|_P\in A_V^P`$ under $`G_V`$. Every finite value pattern is realized, because all maps X→$`A_V`$ are source arrows. At a Henkin target the designated group is trivial. Different target branches are independent. Hence


```math
B_P\cong
 \mathcal P(K^P)\times
 \prod_{V\in\mathcal V}\mathcal P(A_V^P/G_V),
 \tag{10}
```


where $`G_M=1`$ for Henkin targets. This is an externally complete algebra of admitted propositions.

For p pinned by T, let $`\pi_Pp`$ be the least P-pinned upper bound obtained by existentially forgetting the coordinates in $`T\setminus P`$ in each pattern description. The operation preserves target-group invariance. Let $`G_{o,(P)}`$ fix P pointwise.

Exactly as in the [two-object orbit-envelope proof](../../next-update/proofs/infinite-colour-conditional-completeness-countermodel.md), §4,


```math
\pi_Pp=
 \sup_B\{\rho_gp:g\in G_{o,(P)}\}.
 \tag{11}
```


For clarity, the leastness argument does not take the orbit's raw union. If an upper bound u with finite pin R failed to contain $`\pi_Pp`$, choose the conflicting pattern on $`P\cup R`$ and a compatible p-witness on $`P\cup T`$. A member of $`G_{o,(P)}`$ moves $`T\setminus P`$ outside $`P\cup R`$, within its original infinite colour classes. The two finite patterns can then be amalgamated. On an old branch every finite map extends to a source arrow; on the self branch every finite colour pattern is realized using distinct images. This contradicts u bounding the entire orbit.

If $`Y:tt`$ is an admitted source predicate with pin P, its actual extension $`\mathcal F`$ is $`G_{o,(P)}`$-invariant. This follows from symmetry at g and P-pinning at g and the identity. The element


```math
u=\bigvee_{p\in\mathcal F}\pi_Pp
 \quad\text{formed in the complete algebra }B_P
 \tag{12}
```


is therefore the actual least upper bound of $`\mathcal F`$ in B: any admitted upper bound bounds every orbit, hence every $`\pi_Pp`$, and consequently u.

This proves $`BC_t`$. The construction chooses a bound for a fixed admitted family; it does not admit a uniform join operation.

## 5 Whole logical readers and full typed separation

Fix an old object $`V_0`$ for use as a baseline. An evaluation character associated with an arrow b is denoted $`\chi_b(q)=q(b)`$.

For a selected arrow b agreeing with $`\beta_V`$ outside P, the character $`\chi_b`$ is invariant under $`G_{o,(P)}`$, because $`bg=b`$ for every such g. For a finitely supported source permutation b, enlarge P to contain its support; then b commutes with every $`g\in G_{o,(P)}`$, and target symmetry of propositions gives the same character invariance.

On the source colour chart $`\beta h|_P=\beta|_P`$, choose $`g_h\in G_o`$ extending $`h|_P`$. Define


```math
O(h,q)=
 \begin{cases}
 q(bg_h^{-1}),&
 h:o\to o,\ \beta h|_P=\beta|_P,\\
 q(\beta_{V_0}),&
 h:o\to o,\ \beta h|_P\ne\beta|_P,\\
 q(1_V),&h:o\to V\text{ old}.
 \end{cases}
 \tag{13}
```


The proof of well-definedness and source covariance is the same explicit stabilizer calculation as in the two-object model: two extensions differ by a member of $`G_{o,(P)}`$, and for $`\mu\in G_o`$ one may use $`g_{\mu h}=\mu g_h`$. The off-chart baseline is globally $`G_o`$-invariant. At an old target V, the identity row is symmetric because $`q(\mu)=q(1_V)`$ for $`\mu\in G_V`$.

At an ordinary target, transporting O gives the whole identity observer: every subsequent old row in (13) is again identity truth. At a Henkin target the row is the admitted identity operation. Thus the higher landing requirements are satisfied.

Every source self-row reads a selected arrow followed by a source permutation, a source permutation alone, or the baseline arrow. Their typed actions are onto by §3. Every old-target row reads an identity arrow. Consequently for any future row, its evaluation arrow a, any type $`\sigma`$, and any arbitrary predicate F at that row's source,


```math
\bigwedge_{z\in D_\sigma(\mathrm{cod}a)}F(a,z)
 =
 \bigwedge_{x\in D_\sigma(\mathrm{dom}a)}
             F(a,\rho_a x).
 \tag{14}
```


The analogous equality holds for existential joins. These are the full quantifier-operation identities, since both the future row and F were arbitrary. Boolean preservation is immediate. Thus O is whole Good for every finite list, not just materially qualified at the current point.

To separate different propositions, take an arrow h distinguishing them and a finite common pin P. For an old target replace h by the selected arrow agreeing on P; for a self target replace h by a finitely supported permutation agreeing on P. Equation (13) then supplies the required current reader.

For different relations, start with a profile difference at an old h and an arbitrary target tuple. First replace h by a selected arrow b agreeing on the relations' pins, preserving the profile difference at the same tuple. Then lift the tuple along b using §3. This order matters: the original h need not be onto. The resulting two source proposition values are different, so a reader distinguishes them. For a self h, use its bijective transport. This proves full typed OS.

One can either obtain current all-type BF from the established observer theorem or verify it directly. If a future row $`F(h,z)`$ is relevant to a Barcan instance, replace h on a finite pin of F by a selected b and lift z along b. Since $`F(h,z)=F(b,z)`$, every future witness has a current representative at an agreeing arrow. This proves $`BF_{\mathrm{all}}`$ at o. No assertion is made that arbitrary old arrows become onto.

## 6 Simultaneous possibilities and arithmetic scope

The construction preserves every old interpretation exactly. Therefore, if a pure sentence $`\varphi_i`$ holds at an old object $`V_i`$, then


```math
o\models\Diamond\varphi_i.
 \tag{15}
```


For any set-sized list of such witnesses, all the assertions (15) hold at the same source satisfying (1). Optional assumptions describing a target are included inside its witnessed sentence; they are not added as source assumptions.

Choosing one-world Henkin witnesses for every C+Ext-consistent pure sentence supplies all their possibilities simultaneously. Adding other permitted components does not disturb these witnesses. In particular, one may add the finite-support permutation target and obtain


```math
C+OS+BC_t+BF_{\mathrm{all}}
 +\Diamond(\Box ND_t\land\neg BC_t)
```


together with all those extensional Henkin possibilities. This is stronger than separate per-target constructions.

There is an exact reason not to omit the Henkin qualification or call the finite-support class C-complete. In a wholly ideally-full finite-pin model, the predicate whose row consists of the standard closed numeral entities is empty-pinned and symmetric. The defining Frege induction therefore makes finite cardinality standard. At any point satisfying $`I_\sigma=\Diamond I_\sigma^*`$, the numeral entities are distinct: a future witness to $`I_\sigma^*`$ separates them, and identity transports forward. The ordinary standard addition and multiplication graphs are likewise admitted as empty-pinned symmetric row profiles. Thus arithmetic under $`I_\sigma`$ is standard throughout that class, yielding the recorded Necessity of Arithmetic schema.

The mixed construction does not add those external predicates to a Henkin target. Its target-row restriction admits only the original Henkin tables there, so opposite Henkin arithmetic theories remain intact. Arbitrary intensional Henkin targets still require a separate admission argument and are not covered by this theorem.

## 7 What this proves about the remaining consistency question

The source has no true atom. Given any true proposition p pinned by P, choose $`a\notin P`$. Let r have self row $`r(h)=[\beta h(a)=\beta(a)]`$ and zero old-target rows. This is an admitted proposition pinned by $`\{a\}`$. Both p and r are true at the identity, so $`p\land r\ne0`$. A source permutation fixing P can send a to another colour, since there are at least two infinite colour classes. At that permutation p remains true and r is false. Thus $`0<p\land r<p`$. Every true proposition has a nonzero proper part, proving $`\neg\mathrm{Actuality}`$.

The theorem supplies one complete observer source for any set-many permitted targets, including combinations of nonextensional completeness failures and opposite extensional Henkin arithmetic theories. It does not establish


```math
\mathrm{Con}\bigl(C+\mathrm{Max}(C)+OS+BC_t\bigr).
```


Pure Maximalism here must refer to every pure sentence consistent with C itself. The permitted mixed target class has not been shown to realize every such sentence. No replacement of that reference theory by C+Ext or by the theory of the semantic class is intended.

## 8 Sources and verification scope

- **New result:** `misc`, this note, §§1–7; OpenAI Codex, 25 October 2026, unpaginated.
- **Starting construction and complete calculations:** [Infinite colour symmetry and failure of conditional completeness persistence](../../next-update/proofs/infinite-colour-conditional-completeness-countermodel.md), especially §§2–6.
- **Symmetric finite-support framework:** [Symmetric ideally-full models](../../classicism-results-2026-10-24-v2/source/topics/classicism/groups/symmetric-ideally-full.yaml), citing Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, Definitions 15–18, p. 8, §3.1, p. 9, Lemma 21, p. 10, and Proposition 22, p. 11.
- **Landing method for restricted target domains:** [Coalesced finitely pinned interpretation root](../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/coalesced-pinned-interpretations-root.md), the construction and model-of-C verification. That source supplies the landing method, not the new completeness cover.
- **Arithmetic scope:** [Necessity of Arithmetic](../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/necessity-of-arithmetic.yaml) and the standard-numeral arguments in the linked symmetric-model framework.

The general finite-support lift and reader calculations, and the additional Henkin row condition, were independently checked by other OpenAI Codex research agents before this draft was saved. No human verification or Lean formalization is claimed.
