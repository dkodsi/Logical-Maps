# C5 and Functional Choice do not entail Necessity of Analysis

25 October 2026. Ordinary mathematical proof and source audit by OpenAI Codex, prompted by Daniel Kodsi. The new contribution is the explicit transfer to the native relational schema, the choice-preserving package, and the comparison with a CH-preserving variant. No claim of historical novelty or Lean certification is made.

## 1. Result and its precise scope

In a ZFC metatheory with constructible ground universe, there is a model of the map's fixed relational Classicism satisfying

```math
C5+\text{Functional Choice}+\Box\text{Relational Choice}
 +\text{Rigid Comprehension}+\text{Boolean Completeness}
 +\mathrm{Inf}_e+\mathrm{Inf}_t
```

in which **Necessity of Analysis fails**. Here Functional Choice, Rigid Comprehension and Boolean Completeness are **unboxed**; $`\mathrm{Inf}_e,\mathrm{Inf}_t`$ are fresh shorthand for the quantified axioms of infinity, not the framework's distinct $`I_\sigma^*`$ principles. The model also satisfies boxed BF. It can be chosen so that the continuum hypothesis holds in every real-number structure necessarily. Thus even adding Non-contingency of CH to the displayed package does not yield Necessity of Analysis.

This is a relative model construction over ZFC + V=L, which has the usual consistency strength of ZFC. The proof uses Boolean-valued forcing calculations, not an assumption that a countable transitive model or a generic filter exists in the ambient universe. The ground-model requirement is explicit: the particular sentence below is already false in a ground universe containing nonconstructible reals.

The target is exactly `necessity-of-analysis`. For every admitted type $`\sigma`$ and every **first-order** sentence $`\varphi`$ in the ordered-field language **with the natural-numbers predicate**, its instance is

```math
\Box U_{\sigma,\varphi}\ \lor\ \Box U_{\sigma,\neg\varphi},
 \qquad
 U_{\sigma,\varphi}:=
 \forall\mathfrak R\,
   (\mathrm{Real}_\sigma(\mathfrak R)\to\varphi(\mathfrak R)).
```

`Real` uses the carrier, order, ternary addition and multiplication graphs, zero, one and the least inductive natural-number predicate. Completeness concerns **nonempty** bounded subproperties. The failure below is at $`\sigma=t`$. Its witness is a finite, parameter-free first-order analytical sentence expressing that every real is constructible. It is not a CH sentence, a pure ordered-field sentence, or a claim about Analytic Necessitism.

The bare-C5 separation is already reported by Bacon, draft of 9 October 2025, pp. 22–23 and note 55. The snapshot's assertion that this question is open conflicts with that passage. The cited passage also identifies the nonconstructible-real witness; the detailed native model and additional-premise audit below are our connecting argument. [Bacon, §5](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).

## 2. The full Boolean-valued model

Work in a ground universe $`V\models\mathrm{ZFC}`$. Let $`A`$ be a nontrivial complete atomless Boolean algebra and put

```math
B=2\times A,\quad a=(1,0_A),\quad b=(0,1_A).
```

Fix a nonempty ground set $`E`$, and use precisely the admitted relational types:

```math
D_e=E,\qquad D_t=B,\qquad
 D_{\sigma\to\rho}=D_\rho^{D_\sigma}\quad(\rho\ne e).
```

All these function spaces are formed in the ground universe. Application and abstraction are ordinary application and abstraction. Connectives are the Boolean operations of $`B`$; quantifiers are meets and joins. At every type, identity has value $`1_B`$ for equal ground entities and $`0_B`$ otherwise. Truth at the designated point is the first coordinate, $`\pi:B\to2`$. Write $`\rho:B\to A`$ for the second projection.

The construction is Bacon's full Boolean-valued construction, Appendix B.2, specialized to the relational type grammar and to the choices of $`A,E`$ specified here. Its native verification is also recorded in `full-boolean-valued-atom-and-atomless`; the current local and upstream definitions of its forcing algebra differ, as explained in §8. [Bacon, Appendix B.2, pp. 7–9 of the appendix](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).

Every H-theorem has value $`1_B`$: Boolean operations validate its propositional rules, complete meets and joins validate the quantifier rules, crisp identity validates reflexivity and substitution, and beta and eta are literal function equalities. If H proves equivalence of two formulas, their Boolean values agree for every assignment; the corresponding abstractions are therefore the same functions. This validates precisely the theoremhood-restricted Logical Equivalence rule of C. No equivalence under an optional premise is used.

Because the map defines $`\Box p`$ by $`p=\top`$,

```math
\llbracket\Box\psi\rrbracket=
 \begin{cases}1_B&\llbracket\psi\rrbracket=1_B,\\
 0_B&\text{otherwise.}\end{cases}                 \tag{1}
```

Both coordinate projections preserve all set-indexed meets and joins. In particular $`\pi`$ makes the designated first-order quantifiers ordinary quantifiers over the displayed ground domains. C's rules remain sound at the designated point.

## 3. The extensional forcing transfer lemma

The important restriction is to **extensional, box-free structure formulas**. Quantified predicates and graphs are relations on finite powers of the one chosen carrier. They occur only as relation symbols applied to carrier elements, never as arguments to predicates of higher order; equality is used only for elements of that carrier. No assertion is made that the entire typed language, including higher-type identity or the defined box, has the ordinary interpretation in a Boolean-valued universe.

**Lemma.** Let $`S\subseteq D_\sigma`$ be a ground set with two fixed distinct labels $`s_0,s_1`$. Suppose

```math
V\models |\mathbb R|\le |S|,
 \qquad
 1_A\Vdash |\mathbb R|\le |\check S|.
```

For every sentence $`\varphi`$ of the first-order analytical language there is a single tuple $`\mathfrak R_*`$ in the typed model such that

```math
\llbracket\mathrm{Real}_\sigma(\mathfrak R_*)\rrbracket=1_B,
 \qquad
 \llbracket\varphi(\mathfrak R_*)\rrbracket
 =\bigl(\mathbf1_{V\models\varphi(\mathbb R)},
          \|\varphi(\mathbb R)\|_A\bigr).           \tag{2}
```

The same assertion applies to finite second-order analytical formulas that use relation variables only extensionally, including CH.

**Proof.** Choose a ground injection $`j_0:\mathbb R^V\to S`$ sending 0 and 1 to $`s_0,s_1`$. In $`V^A`$, choice and the Boolean maximum principle supply a name $`\dot j`$ forced to be an injection of its real field into $`\check S`$, with those same images of 0 and 1. The anchoring is obtained by a finite permutation of the codomain of any injection. This is metatheoretic choice in ZFC, not object-language Functional Choice.

Pull the ground real field and its natural numbers back to $`\mathrm{ran}j_0`$. For the second coordinate pull the Boolean-valued real field back to $`\mathrm{ran}\dot j`$. For example, at ground labels $`s,t,u\in S`$, the second coordinate of the sum graph is

```math
\|\exists x,y,z\in\mathbb R\,
 (\dot j(x)=\check s\land\dot j(y)=\check t\land
  \dot j(z)=\check u\land x+y=z)\|_A.
```

The carrier's second coordinate at $`s`$ is $`\|\check s\in\mathrm{ran}\dot j\|_A`$. Define order, product and $`N`$ similarly; all relations have value zero outside $`S`$ in the relevant coordinates. Pair each ground characteristic function with the corresponding $`A`$-valued function. Fullness places the resulting curried graphs in the required relational types. Zero and one are the fixed ground labels, so no name for a new individual constant or unavailable operation type is introduced.

For a fixed ground set $`T`$, names for subsets of $`\check T`$ are represented, up to Boolean equality of value one, by functions

```math
f:T\to A,\qquad
 f(t)=\|\check t\in\dot Y\|_A.
```

Conversely every such function gives the normalized name
$`\{(\check t,f(t)):t\in T\}`$. Apply this with $`T=D_\sigma^k`$ for every required finite arity. The second projections of our full typed relation domains contain **all** these functions; their first coordinates may be chosen arbitrarily. Thus relation quantification in the extensional fragment covers all internal subset names, including new subsets of the carrier.

Quantification over the check of a ground set reduces to meets or joins over its ground labels. This remains true for mixed names: their equality values with ground labels cover their membership value in that check set, and substitution for extensional formulas supplies the reduction. Induction on formulas therefore identifies their second-coordinate evaluation with Boolean-valued set-theoretic evaluation. At the first coordinate, the same induction is the usual full extensional interpretation in $`V`$.

Carrier identity causes no mismatch. Distinct ground labels are necessarily distinct checks, and the named injection is injective, so the pulled-back field has precisely this equality on its carrier. We do not replace identity of two predicate entities by equality of their extensions.

The field axioms, nonempty bounded completeness and the least-inductive-subproperty clause for $`N`$ all lie in this extensional fragment. The availability of all subset names is essential for the last two clauses. They hold in each coordinate, proving the first part of (2); formula induction gives its second part. This proves the lemma.

**Uniform consequence.** Put $`\varepsilon=\mathbf1_{V\models\varphi(\mathbb R)}`$ and $`p=\|\varphi(\mathbb R)\|_A`$. At a carrier type meeting the lemma's capacity condition,

```math
\llbracket U_{\sigma,\varphi}\rrbracket=(\varepsilon,p),\qquad
 \llbracket U_{\sigma,\neg\varphi}\rrbracket=(1-\varepsilon,\neg p). \tag{3}
```

For the lower bounds, every tuple satisfying `Real` in either coordinate is an internally complete ordered field with its standard natural numbers, and hence is isomorphic to that coordinate's standard real field. This argument applies below the Boolean value of `Real` even when that value is not one. Isomorphism invariance gives the indicated lower bounds on every implication. Taking their meet preserves them. The tuple in (2) gives the reverse bounds.

It follows from (1) and (3) that this instance of Necessity of Analysis holds exactly when $`A`$ forces $`\varphi`$ to have its ground-universe truth value. The entire schema holds if forcing preserves every parameter-free first-order analytical truth; conversely, if one carrier type has the stated capacity, the schema implies that preservation. Sufficiency does not require real structures at every type: the same isomorphism argument works where they exist, and the other cases are vacuous.

This gives a general explanation of the separation: the model's necessity of analytical truth is exactly the relevant forcing absoluteness, rather than a consequence of its stable identity relation. The familiar coding of subsets of naturals by reals identifies these parameter-free analytical sentences with parameter-free projective sentences.

## 4. A sentence in the exact native grammar

Fix a parameter-free $`\Sigma^1_2`$ predicate $`\mathrm{Constr}(U)`$ defining the constructible subsets of $`\omega`$. Then

```math
\forall U\subseteq\omega\ \mathrm{Constr}(U)           \tag{4}
```

has a $`\Pi^1_3`$ presentation. The descriptive-set-theoretic input is standard and explicitly noted by Veličković and Woodin, Introduction, p. 1; we use that definability theorem, not a substitute assertion about arbitrary countable models of set theory. [The complexity of the reals in inner models of set theory](https://arxiv.org/abs/math/9501203).

For clarity, the interpretation into the permitted first-order language is concrete. Code a subset $`U`$ by

```math
c_U=\sum_{n\ge0}\frac{1+\mathbf1_U(n)}{4^{n+1}}.
```

This sum describes the external coding, not an infinitary object-language formula. With number variables restricted by $`N`$, the graph of $`p=4^{n+1}`$ is arithmetically definable by finite-sequence coding. The conditions

```math
k\le pc<k+1,\qquad k=4q+d,\qquad d\in\{1,2\}
```

define the successive digits using only field relations and $`N`$. Let `Code(c)` require $`0<c<1`$ and that every digit is 1 or 2; let `Bit(c,n)` mean that the digit is 2. The tail after any digit is strictly between zero and one in the scaled expansion, so these definitions have no endpoint ambiguity. Every subset of $`\omega`$ has exactly one such code, and every code determines such a subset.

Translate set quantifiers in (4) into quantifiers over `Code` reals, numerical quantifiers into quantifiers restricted by $`N`$, and membership into `Bit`. This yields one finite first-order analytical sentence $`\varphi_L`$. Eliminate sum and product terms by fresh field variables and the total unique ternary graphs. All remaining variables range over the real-field carrier; there is no higher-type relation quantifier inside $`\varphi_L`$. In every ZFC universe,

```math
\varphi_L(\mathbb R)\quad\Longleftrightarrow\quad
 \mathcal P(\omega)\subseteq L.
```

The detailed digit definitions, proof of surjectivity and relational-term elimination are in [the sentence audit](analytical-sentence.txt).

## 5. One Cohen real gives the countermodel while preserving CH

Now take $`V\models\mathrm{ZFC}+V=L`$,

```math
A=\mathrm{RO}(\mathrm{Add}(\omega,1)),\qquad E=\omega.
```

The forcing adds a subset of $`\omega`$ outside the ground universe. Forcing does not change ordinals or the constructible hierarchy, so

```math
V\models\varphi_L(\mathbb R),\qquad
 1_A\Vdash\neg\varphi_L(\mathbb R).                         \tag{5}
```

Both coordinates satisfy CH. The ground universe does by $`V=L`$. Cohen forcing is countable and ccc, preserves $`\omega_1`$, and has at most
$`(2^{\aleph_0})^{\aleph_0}=\aleph_1`$ nice names for reals in this ground universe. The old reals supply the matching lower bound in the extension.

The Cohen algebra has ground cardinality $`2^{\aleph_0}=\aleph_1`$: a countable base gives the upper bound; joins of arbitrary subfamilies of a countably infinite antichain give the lower bound. Hence $`|B|=\aleph_1`$, and $`A`$ forces that $`\check B`$ and the reals both have cardinality $`\aleph_1`$. The transfer lemma applies at $`\sigma=t`$ with $`S=B`$. We can even choose bijections in both coordinates, so the mixed field uses **the entire same carrier $`D_t`$**, with fixed zero and one and varying order, field graphs and natural-number predicate.

Equations (3) and (5) give the exact values

```math
\llbracket U_{t,\varphi_L}\rrbracket=a,
 \qquad \llbracket U_{t,\neg\varphi_L}\rrbracket=b.
```

Neither value is top. Each box in the target instance is therefore bottom, and the instance has value $`0_B`$, so it is false at the designated atom.

For CH, the extension of the transfer lemma to extensional second-order formulas applies. Both coordinate universes satisfy CH, so every native `Real` structure at every type satisfies its relational CH sentence whenever it exists. Thus $`\Box U_{\sigma,\mathrm{CH}}`$ has value $`1_B`$ for every $`\sigma`$: the model satisfies `non-contingency-of-ch`, indeed its CH disjunct everywhere. Failure of Necessity of Analysis here cannot be inferred from CH contingency; there is none.

## 6. The additional premises

All claims in this section concern every admitted instance unless a type is specified.

**C5 and boxed BF.** Identity and distinctness are crisp, so their boxed-ND instances and the outer boxes have value one. Moreover
$`\bigwedge_x\Box P(x)=\Box\bigwedge_xP(x)`$: each side is one exactly when every value of $`P`$ is top, and is zero otherwise. Thus boxed BF also holds.

**Functional Choice at the designated atom.** If a ground relation $`U`$ is serial there, each of its first-coordinate fibres is nonempty. External choice selects one output in every fibre. For a relational output type the resulting ground function belongs to the full admitted operation domain. Its selecting formula has first coordinate one. If seriality is false, the implication is already true. This proves all unboxed Functional Choice instances, with no claim that their full Boolean values are top.

**Boxed Relational Choice.** Well-order the ground output carrier and define

```math
T(x,y)=U(x,y)\wedge\neg\bigvee_{z<y}U(x,z).
```

For each $`x`$, the values $`T(x,y)`$ are disjoint and their join equals $`\bigvee_yU(x,y)`$. To see the equality of joins, any nonzero part of the latter meets a first $`U(x,y)`$ in the well-order, and hence meets its disjointified part. Inclusion $`T\subseteq U`$ has value one; crisp equality and disjointness make uniqueness have value one. If seriality has value $`c`$, the functional-subrelation assertion for $`T`$ has value at least $`c`$. Thus each Relational Choice implication is top, as is its box. This argument admits individual outputs: $`T`$ is a relation ending in $`t`$, not an operation ending in $`e`$.

**Unboxed Rigid Comprehension.** Replace a relation's first-coordinate extension by its crisp characteristic function $`Y`$, taking only $`0_B,1_B`$. It is a ground relation in the full domain and is coextensive with the original at the designated atom. It is persistent. For any comparison relation $`Z`$, the statement that every $`Y`$-tuple necessarily satisfies $`Z`$ is the same crisp condition as $`Y\le Z`$; this validates inextensibility with value one. Hence $`Y`$ is rigid with value one and supplies the required unboxed coextension.

**Unboxed Boolean Completeness.** At every relational type the carrier is a complete pointwise Boolean algebra. Its algebraic order has crisp truth values, because it is defined by equality of a join with its proposed upper endpoint. Given a property $`F`$, take the external meet of its first-coordinate extension in that complete algebra. The resulting ground entity is its GLB at the designated atom. This proves the full unboxed schema.

**Quantified Infinity at $`e`$ and $`t`$.** Both ground carriers are infinite. At any infinite carrier, the iterated finite numerals are distinct: their values on crisp finite subsets distinguish them. Their crisp characteristic family is inductive and excludes every other candidate from the least inductive family of finite cardinalities. Conversely finite induction puts each iterate into that family. The $`n`$-th numeral has value zero on the universal property of an infinite crisp-identity carrier. Consequently the existential assertion that a finite cardinality holds of the universal property is zero, and the quantified infinity sentence is top. The model therefore validates each requested quantified axiom, and its box as well; no new database ID for a boxed quantified axiom is assumed.

The independent model audit gives expanded calculations and locators: [Boolean model audit](boolean-model-audit.txt).

## 7. Why boxing Functional Choice changes the answer

The countermodel **does not** preserve boxed Functional Choice. Consider

```math
R(p,q)=(p\land q=\top)\lor(\neg p\land q=\bot).
```

It is serial and functional with value one. For a ground operation $`f:B\to B`$, its selecting value $`c_f=\bigwedge_p R(p,f(p))`$ lies below either $`p`$ or $`\neg p`$ for each $`p`$. Every nonzero such $`c_f`$ is an atom. Conversely every atom is obtained by the corresponding decision function. Thus the join of all selecting values is the atomic part of $`B`$, exactly $`a`$. This Functional Choice instance is true at the designated point and has a false box.

Boxed Rigid Comprehension also fails. A rigid relation here must be crisp, since persistence has the form $`\Box\forall x(Yx\to\Box Yx)`$. For the unary property $`X(p)=p`$, the coextension value of any crisp candidate $`Y`$ is a meet deciding every $`p`$; its nonzero values are precisely bounded by atoms. Taking all candidates gives $`a`$, not top. Thus its necessary rigid-coextension assertion is false.

There is a positive boundary already proved in the snapshot:

```math
\Box\text{Functional Choice}
 \Longrightarrow\Box\text{Plenitude}
 \Longrightarrow C5+\text{Atomicity}
 \Longrightarrow C5+\Box\text{Rigid Comprehension}
 \Longrightarrow\text{Necessity of Analysis}.
```

The last step is the existing analytic-necessitism route, not a new result of this note. Thus adding boxed Functional Choice cannot preserve this counterexample. The stronger boxed premise settles the target positively, without needing C5 as a separate assumption. The exact proved-record chain is saved in the database evidence.

## 8. Source comparison and database transfer

The comparison uses public snapshot `a89a5058ebbd5ebe93aec07d47a1a32e3b93f8bb`, decoded at `/tmp/classicism-upstream-a89a5058-decoded.json`. The native checkout lacks `necessity-of-analysis`. Its older Boolean model fixes the regular-open algebra of the real line, whereas the snapshot's model chooses the forcing by CH cases. Under a constructible ground universe the snapshot takes
$`A=\mathrm{RO}(\mathrm{Add}(\omega,\omega_2))`$.

That **existing upstream construction also witnesses the separation**, when the constructible ground is made explicit. Put $`\kappa=\omega_2`$. Under GCH the forcing completion has cardinality $`\kappa`$, and it forces continuum $`\kappa`$. Choose $`S\subseteq B`$ of size $`\kappa`$, a ground subcarrier of size $`\omega_1`$, and the two anchored injections used in §3. The carrier capacity condition holds; the same $`\varphi_L`$ changes truth. Its original singleton individual domain retains quantified Infinity at $`t`$, but fails it at $`e`$. Taking $`E=\omega`$ is a separate variant and retains both.

Do **not** append an unconditional failure of Necessity of Analysis to an unspecified-ground version of the existing model. The constructible-ground assumption supplies this witness. More generally §3 ties its exact truth to parameter-free analytical forcing absoluteness. The one-Cohen model of §5 is a separate forcing choice that additionally preserves CH.

Suggested new model name: **Full Boolean-valued model with one atom and a Cohen component over a constructible ground**. A suitable new ID, if later authorized, is `full-boolean-valued-atom-and-cohen-constructible-ground`. Its definition should set $`E=\omega`$ and $`A=\mathrm{RO}(\mathrm{Add}(\omega,1))`$ over a ZFC + V=L ground. Existing record IDs should remain unchanged.

The newly established separation has premises `necessary-distinctness-necessary-r` and `functional-choice-r`, and target `necessity-of-analysis`. Explicit further holds established above are `necessary-barcan-r`, `necessary-relational-choice-r`, `rigid-comprehension-r`, `boolean-completeness-r`, `axiom-of-infinity-e`, `axiom-of-infinity-t`, and `non-contingency-of-ch`. Explicit failures are `necessity-of-analysis`, `necessary-functional-choice-r`, and `necessary-rigid-comprehension-r`. Atomicity at $`t`$ also fails directly because the second factor is atomless. Other consequences may be derived by the proved-only engine rather than copied into a proposed assertion list.

Independence/non-entailment belongs in a **model** record, not an implication result. The direct source for the connecting proof in §§3–7 is this note (`misc`, unpaginated); Bacon's construction and first-order contingency observation should retain their separate attribution. The original model's authorship, history, certificate date and existing Lean status must not be overwritten. The proposed variant and this proof have no Lean certificate, and no human `checked_by` entry is claimed.

The proved-only baseline engine finds neither entailment, exclusion, nor a recorded separating model for C5 alone or C5 + unboxed Functional Choice against this target. That absence was a database gap, not evidence of an open literature problem. No live records, papers, submission pages, generated maps or Lean files were changed by this research pass.
