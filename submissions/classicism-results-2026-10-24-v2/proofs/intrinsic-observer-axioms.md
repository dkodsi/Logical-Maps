# Intrinsic observer axioms and full standard hierarchies

24 October 2026. Ordinary mathematical consolidation by OpenAI Codex, prompted by Daniel Kodsi. Direct source for the assembled formulation and the ZF refinement: **misc**, this note, §§1–7, unpaginated. Inherited arguments are identified in §8.

Two principles suffice over H: **endpoint separation** and **infinitary range comprehension**. Their axioms concern operations, identity and properties; they do not mention models or semantic validity. Among set-sized models, they characterize full standard relational hierarchies up to canonical typed representation. The representation theorem can be proved in ZF, without the Axiom of Choice.

Endpoint separation recovers the stable logical and atomic structure needed to interpret propositions at worlds. Range comprehension makes every externally specified collection available as the extension of a property. Internal Boolean Completeness, already supplied by endpoint separation, can then form every external atomic join. That last step makes the hierarchy full.

The formulation needs only **unboxed unary range comprehension**, at every original input type. General boxed Infinitary Comprehension gives the same class of original typed reducts, with its full infinitary language interpreted ordinarily. Neither Infinity nor Extensionality is imposed.

## 1. The intrinsic axiom system

### The fixed language and observer qualification

Start with H in the original relational type system: base types $`e,t`$, and arrows $`\sigma\to\rho`$ only when $`\rho\ne e`$. Every relational type has the form $`\tau=\sigma_1\cdots\sigma_n t`$, with a finite, possibly empty argument tuple. Write $`X[\bar x]`$ for left-nested application. Types and type lists index schemas externally; there is no quantification over types.

An observer is an admitted operation $`O^{tt}`$. For each finite list $`\Delta`$ of original types, $`\mathrm{Good}_{\Delta}(O)`$ includes these **identities of whole operations**:

```math
\begin{aligned}
(\lambda p.\,O(\neg p))&=(\lambda p.\,\neg Op),\\
(\lambda p,q.\,O(p\land q))&=(\lambda p,q.\,Op\land Oq),\\
(\lambda p,q.\,O(p\lor q))&=(\lambda p,q.\,Op\lor Oq),\\
(\lambda F^{\sigma t}.\,O(\forall x^\sigma Fx))
 &= (\lambda F^{\sigma t}.\,\forall x^\sigma O(Fx)),\\
(\lambda F^{\sigma t}.\,O(\exists x^\sigma Fx))
 &= (\lambda F^{\sigma t}.\,\exists x^\sigma O(Fx))
 \qquad(\sigma\in\Delta).
\end{aligned}
\tag{1}
```

For each $`\sigma\in\Delta`$, also retain the translated equality clauses

```math
\begin{aligned}
&\forall x^\sigma\,O(x=x),\\
&\forall x,y^\sigma\,\forall F^{\sigma t}
  \bigl[O(x=y)\to(O(Fx)\to O(Fy))\bigr].
\end{aligned}
\tag{2}
```

These clauses matter over H and become redundant after C is recovered. Separate endpoint-fixing clauses are unnecessary: Boolean qualification makes $`O\top`$ true and $`O\bot`$ false, and endpoint range then identifies them with the corresponding endpoints. No commutation with the native modality, or with an infinitary connective, is added to (1).

Define

```math
\mathrm{EndVal}(O):=
\forall p^t\,(Op=\top\lor Op=\bot).
\tag{3}
```

Endpoint-valuedness does not assert correctness about current truth. Different endpoint observers can accept different propositions.

### Axiom A: endpoint separation

For every relational $`\tau=\bar\sigma t`$ and every finite $`\Delta`$, require

```math
\forall X,Y^\tau\left[
X=Y\ \leftrightarrow\
\forall O^{tt}\left(
\mathrm{Good}_{\Delta}(O)\land\mathrm{EndVal}(O)
\to\forall\bar x\,[O(X[\bar x])\leftrightarrow O(Y[\bar x])]
\right)\right].
\tag{EndSep}
```

The empty argument tuple is the propositional instance. Write **End** for this full schema, as in the observer hierarchy. It asserts separation by the qualified observers, not merely the existence of one. The full typed scope is used to recover C from H; reduction to one propositional instance is available only once C is already the base.

### Axiom B: infinitary range comprehension

For every original input type $`\sigma`$, including $`e`$, every set $`I`$, and free parameter family $`(a_i^\sigma)_{i\in I}`$, require

```math
\exists R^{\sigma t}\;\forall x^\sigma
\left(Rx\leftrightarrow\bigvee_{i\in I}(x=a_i)\right).
\tag{Range∞}
```

The variables $`R,x`$ are fresh for the parameter family. The instance is required under **every simultaneous assignment** to those parameters. Empty $`I`$, repeated parameter values, and non-well-orderable index sets are allowed. Each instance is set sized, with no fixed cardinal bound. The scheme is fixed independently of the model to which an instance is applied.

Use the ordinary classical infinitary disjunction clause: the disjunction is true exactly when one of its disjuncts is true. For this minimum formulation it suffices to add the displayed range assertions to the language. No infinitary lambda abstraction, new type, infinite argument tuple, or necessary preservation of arbitrary conjunctions is needed for the fullness proof. The original finitary H rules and C's H-theoremhood restriction are unchanged.

The proposed intrinsic package is

```math
\mathsf T_{\mathrm{obs}}:=
\mathrm H+\mathrm{End}+\mathrm{Range}_{\infty}.
\tag{4}
```

“Intrinsic” describes the formulation: its axioms use observers, identity and comprehension rather than an assertion that a model is full. The unrestricted scope of its index and parameter families remains a foundational commitment; §7 explains that scope.

## 2. What endpoint separation already provides

The established finitary characterization is

```math
\mathrm H+\mathrm{End}
\quad\equiv\quad
\mathrm{C5}+\mathrm{Atomicity}_t.
\tag{5}
```

C5 includes C and the separately boxed, universally closed necessary-distinctness instances at all original types. It is not unboxed ND. The proof first forgets the endpoint restriction, obtaining ordinary logical separation and hence C, Barcan and Functionality over H. Opposite endpoint outputs give necessary distinctness. Quantifier preservation and the endpoint diagonal produce atoms. Conversely, principal atom tests provide endpoint separators. See [Logical observer separation, §3](logical-observer-hierarchy.md) and [Typed separation and Classicism, §§2–3](h-observer-space/typed-separation-and-classicism.md).

Consequences already available before Range∞ include all-type Barcan and Functionality, Atomicity at every relational type, Actuality, Boolean Completeness, Plenitude and Rigid Comprehension. Established boxed forms include necessary Atomicity, Actuality, Boolean Completeness and Plenitude. These are finitary C5 consequences, not new consequences attributed to unrestricted range comprehension.

There is a canonical correspondence between atoms and endpoint observers:

```math
a\longmapsto O_a,\qquad O_a(p)=\Box(a\to p);
\qquad
O\longmapsto a_O=\forall p\,(Op\to p).
\tag{6}
```

Under C5, qualification at $`\{t\}`$ suffices for this correspondence, and each resulting observer qualifies at every requested finite list. Actuality supplies the unique true atom. Its observer is the actual-truth evaluator; other atom observers evaluate other complete possibilities. This does not identify a contingent proposition with its actual truth value.

Equation (5) still permits nonfull Henkin hierarchies. Internal Boolean Completeness joins the extension of every **admitted** property; it does not itself assert that every external collection is such an extension.

## 3. How range comprehension supplies fullness

### From range assertions to external atomic joins

Fix a set-sized model of (4), and work first with its current identity quotients. For any external subset $`S\subseteq D_\sigma`$, apply Range∞ with $`I=S`$ and assign the parameter at index $`s`$ to $`s`$. The resulting property has current extension exactly $`S`$. If raw domains contain distinct representatives of one identity class, use all representatives above $`S`$, as detailed in §5.

Fix any external family $`(b_i)_{i\in I}`$ of atoms of a relational type $`\tau`$. Range∞ at **input type $`\tau`$** supplies $`X^{\tau t}`$ whose current extension is the family range. Internal Boolean Completeness at $`\tau`$, in its least-upper-bound form, supplies $`J^\tau`$ such that

```math
\forall Y^\tau\left[
\left(\forall Z^\tau\,(XZ\to Z\le_\tau Y)\right)
\leftrightarrow J\le_\tau Y
\right].
\tag{7}
```

Because the extension of $`X`$ is exactly the family, (7) is precisely its external least-upper-bound condition. This includes the empty family. There is no assumption that $`X`$ is endpoint-valued and no substitution of $`\exists Z(XZ\land Z)`$ for the required join.

Thus every external family of atoms at every relational type has a join. This is the established bridge from actual External Comprehension to Arbitrary Atomic Joins in [Positive results, §5](infinitary-canonical-representation.md).

### The canonical world representation

Let $`W`$ be the set of propositional atoms and $`w_0`$ its unique currently true member. Retain the current identity quotient at $`e`$. For $`\tau=\bar\sigma t`$, represent $`R^\tau`$ by its support

```math
\beta_\tau(R)=
\{(w,\bar a)\in W\times\textstyle\prod_kD_{\sigma_k}:
w\le R[\bar a]\}.
\tag{8}
```

Atom tests preserve Boolean operations. Barcan gives their quantifier clause: if $`w\le Fx`$ for every current $`x`$, then $`\forall x\Box(w\to Fx)`$; BF gives $`\Box\forall x(w\to Fx)`$, hence $`w\le\forall x Fx`$. The converse follows from necessary universal instantiation. Necessary identity and distinctness make equality constant at these worlds. Atomicity and Functionality make the representation faithful at every relational type. They also identify algebraic order with inclusion of supports.

Current truth is truth at $`w_0`$, and native necessity is universal quantification over $`W`$. This establishes a constant-domain world representation of the original typed language before external fullness is assumed. Its domains may at this stage omit some subsets and functions.

### Every world–argument support is represented

For a point $`z=(w,\bar a)`$ in a world–argument product, the ordinary finite term

```math
s_z:=\lambda\bar x.\,
w\land\bigwedge_k(x_k=a_k)
\tag{9}
```

has support exactly $`\{z\}`$. It is therefore an atom of that relation type. For the empty tuple it is the proposition $`w`$.

Let $`U\subseteq W\times\prod_kD_{\sigma_k}`$ be arbitrary. Form the external join $`J`$ of $`\{s_z:z\in U\}`$. Every point of $`U`$ belongs to $`\beta_\tau(J)`$. If $`z\notin U`$ nevertheless belonged to that support, then $`J\land\neg s_z`$ would be a strictly smaller upper bound of all the same singleton atoms. This contradicts leastness. Hence

```math
\beta_\tau(J)=U.
\tag{10}
```

All world–argument supports are represented. In particular, the proposition domain is the full powerset of $`W`$.

For any existing external function $`f:D_\sigma\to D_\rho`$, flatten the relational output type as $`\rho=\bar\tau t`$. The set of $`(w,x,\bar y)`$ satisfying $`w\le f(x)[\bar y]`$ is a support of the preceding kind. Its representing operation has the same value as $`f`$ at each input, by faithfulness. Thus every allowed external function is admitted.

**Representation theorem.** In ZF, the original typed reducts of set-sized models of $`\mathsf T_{\mathrm{obs}}`$ are exactly the full standard relational hierarchies, up to canonical typed representation:

```math
D_e=E,\qquad D_t=\mathcal P(W),\qquad
D_{\sigma\rho}=D_\rho^{D_\sigma}\quad(\rho\ne e),
\tag{11}
```

with nonempty sets $`E,W`$, a designated $`w_0\in W`$, ordinary application, fixed typed domains, identity as equality, and necessity ranging over all of $`W`$.

For the converse, in any hierarchy (11), each $`w\in W`$ determines the admitted reader $`O_w(p)=W`$ if $`w\in p`$, and $`O_w(p)=\varnothing`$ otherwise. These readers preserve the whole ordinary logical operations and separate propositions and relational intensions. For a family $`(a_i)`$, its range is a set; its rigid characteristic property belongs to $`D_{\sigma t}`$ and witnesses Range∞. These constructions require no choice function.

## 4. Equivalent presentations and actual-truth evaluation

Over H+End, the following impose the same class of original set-sized reducts:

| Presentation | Exact additional requirement |
|---|---|
| Infinitary range comprehension | The unboxed Range∞ scheme at every original input type |
| External Comprehension | Every external subset of each current typed domain is the extension of an admitted property |
| External atomic joins | Every external family of atoms at every relational type has a join |
| External Boolean completeness | Every external family of entities at every relational type has a join and a meet |
| Disjunctive boxed comprehension | Every arbitrary set-sized disjunction of finitary matrices, with arbitrary simultaneous parameters, has a representative agreeing necessarily at each finite argument tuple |
| Full Infinitary Comprehension | Every admitted well-founded set-sized infinitary matrix has such a boxed representative, with the ordinary infinitary interpretation |

The first four equivalences follow from §3 and [Positive results, §5](infinitary-canonical-representation.md). Boxed disjunctive comprehension implies Range∞ by using identity matrices and dropping the box. Fullness supplies representatives for the larger infinitary matrices by well-founded satisfaction recursion. The reverse comparisons are therefore equivalences of model classes or canonical expansions; no deduction-system completeness is being used. See [Infinitary Comprehension, §4](infinitary-comprehension.md).

Only the first row is needed in the preferred intrinsic package. The external rows cannot be replaced by internal Boolean Completeness: that principle was available before Range∞ was added.

The actual-truth evaluator connection gives alternative finite components. Put

```math
\mathrm{Eval}(B):=
\forall p\,[(p\to Bp=\top)\land(\neg p\to Bp=\bot)],
\qquad
\mathrm{BE}:=\exists B^{tt}\,\mathrm{Eval}(B).
\tag{12}
```

Let OS be full ordinary logical separation with the same whole-operation qualification. Then

```math
\mathrm H+\mathrm{End}
\equiv\mathrm H+\mathrm{OS}+\mathrm{BE}
\equiv\mathrm C+\Box\mathrm{BE}.
\tag{13}
```

For the middle theory, OS supplies C and BF; BE supplies ND and Actuality; ND with BF gives C5. The actual evaluator becomes fully qualified, and $`B\circ O`$ turns every ordinary separator into an endpoint separator with the same current truth profile. Conversely End gives C5, Actuality and BE.

For the last theory, boxed BE gives C5 and boxed Actuality. The recorded C5 + necessary Actuality implication supplies Atomicity. Conversely C5 + Atomicity gives necessary Actuality and hence boxed BE. C is explicit here; boxed BE alone has not been used to recover C from bare H.

Consequently Range∞ can be added to any theory in (13) to obtain the same full-hierarchy characterization. Each possible world has its own unique actual-truth evaluator. Requiring one fixed evaluator to remain correct everywhere, $`\exists B\Box\mathrm{Eval}(B)`$, instead gives Extensionality over C and is not a replacement for boxed BE in this noncollapsing package.

See [the evaluator ladder](../source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md), [canonical evaluation, §§1–5](../source/research/2026-10-22/proof-refinements/canonical-actual-evaluator.md), and [the endpoint bridge, §§2–3](h-observer-space/plenitude-endpoint-bridge.md).

## 5. Why ZF suffices for the representation

The earlier full-hierarchy presentation used ZFC. The structural proof above can be carried out in ZF. This refines that presentation with the following explicit witness discipline.

First, the finitary endpoint argument chooses a separator or atom only for a fixed input or pair, then generalizes. It does not select witnesses simultaneously for an external family. Worlds are the set of **all** proposition atoms; no ultrafilter theorem or atom-selection function is invoked.

Second, equality quotients need no chosen representatives. If $`\pi:D\to D/{=}`$ is a quotient map and $`S\subseteq D/{=}`$, take the index set $`\pi^{-1}[S]`$ and assign the parameter at index $`d`$ the raw value $`d`$. This definable assignment names all representatives above $`S`$, and its range property descends to exactly $`S`$. The same construction applies to world–tuple families. Indexing by a carrier or its preimage, rather than an ordinal enumeration, matters when that carrier may not be well orderable.

Third, each external support has a unique representing identity class, by faithfulness. Once existence is proved for an arbitrary fixed support, Separation and Replacement form the inverse of the support map. This is unique determination, not selection among multiple distinct identity classes. Singleton tensors and their families are definably formed.

Finally, the support of an already given external function is definable. Representing it never requires choosing its values. The converse full hierarchy, endpoint readers and range properties are canonical ZF constructions. General infinitary matrices, when included, have their truth interpretation by well-founded recursion on set-sized syntax.

The theorem is therefore uniform over the stated ZF setting. No claim is made that ZF is a minimal metatheory.

## 6. Structural consequences and genuine choice points

**Worlds are recoverable rather than primitive.** They may be taken as atoms, or equivalently as the endpoint observers under (6). A proposition is represented by the observers accepting it. Range∞ ensures every external subset of these worlds, and every higher world–argument pattern, is represented.

**Contingency remains.** A full hierarchy with two worlds has propositions true at one and false at the other. It satisfies both axioms and refutes Extensionality. Endpoint-valued observers do not make their inputs endpoint-valued.

**Infinity remains optional.** Neither base set must be infinite. Full hierarchies allow individuals and worlds to be finite or infinite independently. To select the specifically infinite target of the earlier full-Gallin axiomatization note, add the two quantified Frege Infinity axioms at $`e`$ and $`t`$.

**Plenitude and Choice have different roles.** Plenitude represents total single-valued relations; their unique values give a graph in ZF. Functional Choice selects from arbitrary nonempty value sets. Fullness admits any selecting function that exists externally, but it does not prove that such a function exists.

This dependence is exact at the metatheoretic level. Suppose Functional Choice holds in every full one-world relational hierarchy over arbitrary nonempty individual sets. Given a set-indexed family $`(A_i)_{i\in I}`$ of nonempty sets, take an individual set containing disjoint tagged copies of its indices and members, with one default individual. A full relation of type $`e(et)t`$ relates tagged index $`i`$ to precisely the singleton properties of tagged members of $`A_i`$; at other inputs give the default singleton. This relation is serial. Functional Choice supplies an operation assigning one such singleton to each tagged index. Each selected property has a unique member, so Replacement extracts a choice function for the original family. Thus this universal full-model Functional Choice assertion implies AC over ZF. Conversely AC supplies the selecting functions in every full hierarchy at every evaluation world.

The full-model characterization is choice-free, while the further universal validity of Functional Choice, and hence its boxed form, is AC-dependent. These claims concern all full hierarchies; they do not say that every particular hierarchy determines the ambient Axiom of Choice.

## 7. Scope of the characterization

Range∞ includes **arbitrary set-indexed families and simultaneous parameters at every original input type**, including $`e`$. No fixed cardinal bound or finite-parameter restriction supplies unrestricted fullness in general. The bounded-support and elementary-submodel examples in [Infinitary Comprehension, §5](infinitary-comprehension.md) establish those restrictions' failure in ZFC. They are not needed for the choice-free positive proof.

Fullness is relative to the ambient collections. If an inner universe $`M`$ omits subsets present in a larger universe $`V`$, then $`\mathcal P^M(E)`$ may be properly contained in $`\mathcal P^V(E)`$. The scheme interpreted in $`M`$ need not include the new parameter families available in $`V`$. The theorem is a uniform structural characterization relative to those collections, not a claim of universe-absolute fullness.

The result identifies models and gives a canonical representation; it does not claim a complete calculus for all full-standard validities. The established [proof-calculus analysis](atomic-join-calculus.md) states the precise limits for ordinary set-coded infinitary proofs. No further completeness proposal is part of this consolidation. The positive formulation, representation and Choice distinction stand independently of that issue.

## 8. Sources

The assembled intrinsic formulation, specialization to unboxed Range∞, explicit ZF audit, and metatheoretic Choice distinction are ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026; direct source **misc**, §§1–7, unpaginated. Their inherited components are:

1. [Logical observer separation and its hierarchy](logical-observer-hierarchy.md), §§1, 3 and 8: full qualification, endpoint characterization, atom correspondence and evaluator distinction; OpenAI Codex, prompted by Daniel Kodsi, 23–24 October 2026, unpaginated.
2. [Typed separation and Classicism](h-observer-space/typed-separation-and-classicism.md), §§2–3: full typed H recovery; OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, unpaginated.
3. [Arbitrary atomic joins: positive results](infinitary-canonical-representation.md), §5: canonical representation and the equivalence of actual External Comprehension, external joins and fullness; OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026, unpaginated.
4. [Infinitary Comprehension](infinitary-comprehension.md), §§1, 4–5: fixed syntactic schemes, full-hierarchy characterization and parameter scope; OpenAI Codex, prompted by Daniel Kodsi, 23 October 2026, unpaginated. The present ZF proof refines its ZFC ambient presentation.
5. [The actual-truth evaluator ladder](../source/research/2026-10-22/notes/actual-truth-evaluator-ladder.md), levels 2–5 and necessary local evaluation; [canonical actual evaluation](../source/research/2026-10-22/proof-refinements/canonical-actual-evaluator.md), §§1–5; and [the endpoint bridge](h-observer-space/plenitude-endpoint-bridge.md), §§2–3: ingredients of (13); OpenAI Codex, prompted by Daniel Kodsi, 22–24 October 2026, unpaginated.
6. Bacon and Dorr, *Classicism*, draft of 16 May 2023: Proposition 2.4, p. 23 ([ND and BF lift](../source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml)); Propositions 2.5–2.7, pp. 25–26 and 29–30 ([necessary Actuality to Atomicity](../source/topics/classicism/results/c5-and-necessary-actuality-imply-atomicity.yaml), [Atomicity to necessary Actuality](../source/topics/classicism/results/atomicity-t-and-bf-imply-necessary-actuality.yaml), [necessary Boolean Completeness](../source/topics/classicism/results/c5-and-atomicity-imply-necessary-completeness.yaml)); and §2.3, concluding equivalences, p. 33 ([necessary Plenitude](../source/topics/classicism/results/c5-and-atomicity-imply-necessary-plenitude.yaml)). These source proofs retain their own record and verification status.
