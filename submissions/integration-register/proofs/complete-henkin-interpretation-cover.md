# Observer covers and Boolean completeness

Ordinary mathematical research by OpenAI Codex, 26 October 2026. Direct source: misc, §§1–8 below, unpaginated. This extends the [mixed finite-pin and extensional-Henkin cover](mixed-finite-pin-henkin-completeness-cover.md). It does not complete any higher Henkin domain. No native database record, human verification, or Lean certificate is asserted.

There are two results. For the target classes in §1, one observer source preserves all the targets and satisfies $`BC_t`$. For arbitrary C targets, §8 supplies unrestricted observer sources without asserting $`BC_t`$. Applied to the C-complete component family of the original interpretation-root construction, these give pure Maximalism together with full OS, all-type Relational Choice and all-type Zorn, both with Actuality and with its negation. Neither unrestricted result settles the addition of $`BC_t`$.

## 1 The preservation theorem

Work in ZFC and the pure relational language of C. Let a nonempty set-sized family of disjoint C action-model components be given. Each component may be of either of the following kinds.

1. **Complete-Henkin components.** The higher domains are arbitrary Henkin domains. At every object V, the actual proposition Boolean algebra $`B_V=D_t(V)`$ is externally complete. Every old transport $`\rho_k:B_V\to B_W`$ preserves arbitrary external joins, and every old transport at every type is onto.
2. **Finite-pin components.** These are the symmetric ideally-full finite-pin action components permitted in the preceding cover theorem. Their auxiliary carriers are nonempty sets, arrows are functions, and individuals are those carriers or the uniform singleton-individual variant.

There is a single C model with a new source o satisfying


```math
OS+BC_t+BF_{\mathrm{all}}+\neg\mathrm{Actuality},
 \tag{1}
```


in which every given component retains exactly its old objects, arrows, typed domains, operations, and pure truths, and every old object is reachable from o. OS has its full typed scope and original whole-operation qualification at every finite type list.

If all components are of the first kind, the source additionally satisfies


```math
\Box BC_t+\Box BF_{\mathrm{all}}.
 \tag{2}
```


No general claim of $`\Box OS`$ is made. A finite proposition domain automatically satisfies the completeness requirement, and any Boolean transport between finite proposition domains preserves all joins. Thus arbitrary intensional Henkin diagrams with finite proposition domains and onto transports at all types are included.

The first kind includes the earlier one-world extensional Henkin components, but does not require Extensionality. The second kind permits incomplete proposition domains and nononto old transports. In the mixed case only the current assertions in (1) are unconditional.

Any set-many pure sentences witnessed in these permitted components are consequently simultaneously possible at one source satisfying (1). The theorem does not assert that these classes witness every C-consistent pure sentence. It does not preserve arbitrary fixed nonlogical constants simultaneously.

## 2 Typed auxiliary names and the new arrows

Choose an infinite cardinal $`\kappa`$ at least as large as every old typed carrier and every finite-pin auxiliary carrier. This choice concerns only the old diagram. The new source domains need not have cardinality at most $`\kappa`$.

For each type $`\sigma`$, choose a set $`K_\sigma`$ of cardinality at most $`\kappa`$, with at least two elements, admitting a surjection onto $`D_\sigma(V)`$ for every complete-Henkin object V. At type e also require surjections onto the auxiliary carriers of the finite-pin objects. Disjoint unions, two extra points, and selected default values provide these maps.

Put


```math
C_\sigma=K_\sigma\times\kappa,\qquad
 \beta_\sigma(c)=\text{the first coordinate of }c.
 \tag{3}
```


These are auxiliary name sets. Only $`C_e`$ is the individual domain of the source. At every relational type, the source domain will instead consist of profiles, as defined below.

The root endomorphisms and designated symmetry group are


```math
\begin{aligned}
 \mathrm{End}(o)
   &=\prod_\sigma\mathrm{Sym}(C_\sigma),\\
 G_o
   &=\prod_\sigma\prod_{a\in K_\sigma}
       \mathrm{Sym}(\{a\}\times\kappa).
\end{aligned}
 \tag{4}
```


Thus an arbitrary root loop permutes names within their types; a designated symmetry additionally preserves their colours.

For a complete-Henkin object V, an arrow $`I:o\to V`$ is a typed interpretation


```math
I_\sigma:C_\sigma\longrightarrow D_\sigma(V)
 \quad\text{with every fibre of every }I_\sigma
 \text{ of cardinality }\kappa.
 \tag{5}
```


The selected baseline interpretation $`\beta_V`$ is obtained by composing each colour map $`\beta_\sigma`$ with the chosen surjection onto $`D_\sigma(V)`$. Its fibres have cardinality $`\kappa`$. A finite modification of $`\beta_V`$ remains an arrow of form (5).

For an old arrow $`k:V\to W`$ in such a component, define
$`(kI)_\sigma=\rho_k I_\sigma`$. Every $`\rho_k`$ is onto. The inverse image of an element of $`D_\sigma(W)`$ is a nonempty union of at most $`\kappa`$ fibres of size $`\kappa`$, so $`kI`$ again satisfies (5).

For a finite-pin object V with auxiliary carrier $`A_V`$, the arrows $`o\to V`$ are all maps $`h:C_e\to A_V`$. They use no higher-type name coordinates. Precomposition by a typed root loop g uses $`g_e`$. Choose an infinite-fibre baseline $`\beta_V:C_e\to A_V`$ using the colour map at e.

All old arrows remain unchanged, and no old object has an arrow into o. These rules define a category. Into a complete-Henkin object, the individual action is $`I_e`$. Into a finite-pin component it is h or the unique singleton map, according to that component's convention.

For a finite set P of typed names write $`P_\sigma=P\cap C_\sigma`$. Agreement on P between interpretations means agreement in each type. Agreement between finite-pin arrows means agreement on $`P_e`$. These conventions are also used when P contains names that the arrow does not use.

### Uniform interpretations lift through every old arrow

We will use the following exact fact. Let $`k:V\to W`$ be an old arrow between complete-Henkin objects. Suppose I is an interpretation at V and J is one at W with

```math
J|_P=(kI)|_P.
```

Then there is an interpretation L at V such that


```math
kL=J,\qquad L|_P=I|_P.
 \tag{6}
```


At each type, for each $`w\in D_\sigma(W)`$, partition the set
$`J_\sigma^{-1}(w)`$, of size $`\kappa`$, into sets of size $`\kappa`$ indexed by the nonempty set $`\rho_k^{-1}(w)`$, which has size at most $`\kappa`$. Assign each part its indexing value. Prescribe the finitely many names in $`P_\sigma`$ first; their requested values lie in the correct fibres by the hypothesis. Finite rearrangement preserves the cardinalities of all parts. Doing this at each type gives (6).

In particular, for fixed I and P,


```math
\{kL:L|_P=I|_P\}
 =
 \{J:J|_P=(kI)|_P\}.
 \tag{7}
```


This is the only place where onto transport at all old types is required for the envelope's naturality.

## 3 Source domains, landing, and named lifts

Set $`D_e(o)=C_e`$. Define relational source domains recursively. An entity of type $`\tau=\bar\sigma t`$ is a bit profile $`A(h,\bar z)`$, where h ranges over arrows from o and $`\bar z`$ ranges over all appropriate tuples at its target. Require:

- a finite typed pin P such that same-target arrows agreeing on P give identical rows on every target tuple;
- source self-row symmetry $`A(gh,\rho_g\bar z)=A(h,\bar z)`$ for $`g\in G_o`$, and the inherited target symmetries on finite-pin components;
- at every complete-Henkin interpretation I, the full old section
  $`(k,\bar z)\mapsto A(kI,\bar z)`$ is an existing entity of $`D_\tau(V)`$.

The last condition is landing. It determines transport along I uniquely, by faithfulness of old intensions. On an ordinary finite-pin branch, landing is automatic: transport along h is pinned by $`h[P_e]`$, inherits symmetry, and is admitted by the old component's ideal fullness.

Root-loop transport is precomposition:


```math
(\rho_gA)(h,\bar z)=A(hg,\bar z).
 \tag{8}
```


The individual action is the one specified in §2. Application uses the transported arguments. A higher auxiliary name is not itself a source entity and is not counted as a source individual.

For a relational name $`c\in C_\tau`$, define $`\widehat c`$ as follows. Its self rows are zero. At a complete-Henkin interpretation I its row is the actual extension of $`I_\tau(c)`$. Its finite-pin-component rows are zero. This profile is pinned by $`\{c\}`$; at an old future k its row is the extension of $`\rho_kI_\tau(c)`$. Therefore


```math
\rho_I\widehat c=I_\tau(c),
 \qquad
 \rho_g\widehat c=\widehat{g_\tau(c)}.
 \tag{9}
```


For type e, use the literal individual name $`c\in C_e`$, whose image under I is $`I_e(c)`$. It has no zero self-row construction. Since every $`I_\sigma`$ is onto, (9) proves that **every interpretation arrow is onto at every type**.

At a finite-pin target, the earlier finite-section lift remains available. For a selected infinite-fibre map $`b:C_e\to A_V`$ and an old entity A pinned by T, choose $`s:T\to C_e`$ with $`bs=1_T`$. At an old-target map $`l:o\to W`$, give the lift the row $`A(k,\bar z)`$ if an old $`k:V\to W`$ satisfies $`k|_T=ls`$, and zero if no such k exists. Give it zero self rows and zero complete-Henkin rows. Pinning by T makes the row independent of the matching k; symmetry is inherited. At every old future k its transport along b is exactly A, on arbitrary future tuples. The proof in the preceding cover therefore establishes all-type onto transport for these selected maps too.

### Closure under C

The language-closure proof is the interpretation-root proof with the indicated pin conventions. If finitely many parameters have pins with union P, their full transports along same-target arrows agreeing on P are identical: subsequent composition preserves agreement. On a finite-pin branch only $`P_e`$ is used.

At an old object, the row of a term is the old term denotation with these transported parameters. Thus it lands in the original Henkin domain, or is admitted by the old finite-pin framework. At source self rows, the ordinary recursive satisfaction clauses are invariant under the designated group, and agreement on P preserves them. Quantification ranges over the already defined source domain; that domain is closed under the group action. Application and abstraction satisfy the same pin and landing conditions.

Consequently all lambda denotations are admitted, and the usual action-model proof of C applies. In particular, H-equivalent formulas have identical intensions at every arrow and tuple, preserving the original Logical Equivalence gate. No external higher function is inserted into a target Henkin domain.

## 4 Complete fixed-pin proposition algebras

Let $`B=D_t(o)`$, and let $`B_P`$ be the subalgebra of P-pinned propositions. This subalgebra has arbitrary external joins, and these are actual joins in B.

For a family $`(p_i)`$ in $`B_P`$, define its candidate join z as follows.

- At a source self row, take the union of the bits $`p_i(h)`$.
- On a finite-pin old branch, take the union of the profile bits. It is still $`P_e`$-pinned and symmetric. Its transports land by ideal fullness.
- At a complete-Henkin interpretation I, prescribe the old proposition entity


```math
z_I=\bigvee_i\rho_Ip_i
 \quad\text{in }B_V.
 \tag{10}
```


The row at I is the current truth of $`z_I`$. These are not, in general, the unions of the old truth bits.

The prescribed old sections are natural:


```math
\rho_k z_I
 =\bigvee_i\rho_k\rho_Ip_i
 =\bigvee_i\rho_{kI}p_i
 =z_{kI},
 \tag{11}
```


using completeness of the old Boolean transport. Hence the profile lands. It is P-pinned because each whole $`\rho_Ip_i`$ depends only on $`I|_P`$; source symmetry is immediate.

Every $`p_i\le z`$. If u is any admitted root upper bound, then at each complete-Henkin I the whole inequalities $`\rho_Ip_i\le\rho_Iu`$ imply $`z_I\le\rho_Iu`$. The source and finite-pin rows are bounded pointwise. Thus $`z\le u`$. This proves the claim about actual joins, without any assumption that an old truth character preserves arbitrary joins.

## 5 Finite-pin envelopes and current $`BC_t`$

For any proposition p and finite typed P, construct $`\pi_Pp\in B_P`$.

At a source self loop h, set its bit to true iff some loop l agrees with h on P and satisfies $`p(l)`$. At a finite-pin old arrow h, use the analogous existential finite-value pattern on $`P_e`$. The latter profile lands by ideal fullness.

At a complete-Henkin interpretation I, prescribe the old entity


```math
a_I=\bigvee_{L|_P=I|_P}\rho_Lp.
 \tag{12}
```


By (7) and complete old transport,


```math
\rho_k a_I
 =\bigvee_{L|_P=I|_P}\rho_{kL}p
 =\bigvee_{J|_P=(kI)|_P}\rho_Jp
 =a_{kI}.
 \tag{13}
```


This proves landing. All rows are P-pinned and symmetric. Also $`p\le\pi_Pp`$.

The envelope is exactly the least admitted upper bound of the orbit of p under

```math
G_o(P)=\{g\in G_o:g|_P=1_P\}.
 \tag{14}
```


It bounds the orbit: on a complete-Henkin branch, $`Ig`$ occurs among the interpretations in (12), and the other branches follow from the definition.

For leastness, suppose u is an admitted upper bound of this orbit, with pin R, and p has pin T. Consider a complete-Henkin I and any L agreeing with I on P. Choose $`g\in G_o(P)`$ that moves $`T\setminus P`$ outside R, within the infinite colour classes. Amalgamate the finite prescriptions

```math
J|_R=I|_R,\qquad (Jg)|_T=L|_T.
 \tag{15}
```

They are consistent on their overlap. Each finite typed prescription extends to a uniform interpretation J by finite modification of a baseline. Pinning gives equalities of whole old entities, so

```math
\rho_Lp
 =\rho_J(\rho_gp)
 \le\rho_Ju
 =\rho_Iu.
 \tag{16}
```

Taking the join in (12) proves $`a_I\le\rho_Iu`$. This whole-entity comparison is essential; it does not infer a join inequality from merely accepted old propositions.

On a finite-pin branch, the same fresh g moves the relevant individual names outside the pin of u. Amalgamate the two finite value maps and extend to a root map into the old carrier. Collisions are allowed there. The resulting bit comparison gives the finite-pin envelope below u.

For completeness, source self rows require one additional adjustment because their arrows are permutations. If l agrees with h on P and $`p(l)`$ holds, first choose a colour-preserving target permutation $`\mu`$ fixing $`h[P]`$ and moving $`l[T\setminus P]`$ away from $`h[R]`$. Symmetry preserves $`p(\mu l)`$. Choose g as above. The partial prescriptions $`j|_R=h|_R`$ and $`(jg)|_T=(\mu l)|_T`$ now form an injective typed partial map, and extend to a root permutation j. The orbit upper-bound property gives $`u(j)`$, hence $`u(h)`$. This proves leastness on self rows as well.

Now let $`Y^{tt}`$ be any current admitted predicate, pinned by P. Its actual extension

```math
S=\{p\in B:Yp\text{ is currently true}\}
```

is invariant under $`G_o(P)`$. Indeed symmetry transports the input by g, while pinning identifies the row of Y at g with its row at the identity.

By §4 the following join exists in $`B_P`$:


```math
b=\bigvee_{p\in S}\pi_Pp.
 \tag{17}
```


It bounds S. Any actual upper bound of S bounds each $`G_o(P)`$-orbit in S, hence every $`\pi_Pp`$, hence b. Thus b is the actual least upper bound of the current extension of Y. Boolean duality gives $`BC_t`$.

This argument produces each required join separately. It asserts no admitted operation choosing all current joins.

## 6 Whole logical observers and full typed separation

Call a root arrow selected if it is a finite modification of one of the baselines, or a root permutation with finite support in the typed name sets. Selected complete-Henkin arrows are uniform interpretations. Selected finite-pin arrows are infinite-fibre surjections and have the lifts of §3.

For each selected b, let $`\chi_b(q)=q(b)`$. There is a finite typed P such that $`\chi_b`$ is invariant under $`G_o(P)`$. For a modified baseline, include all modified names in P. Then $`bg=b`$ for $`g\in G_o(P)`$. For a finite-support root permutation, include its support: it commutes with $`G_o(P)`$, and source symmetry of q proves the same invariance.

Fix any one old baseline $`\beta_*`$. For a root loop h on the colour chart

```math
\beta_\sigma h_\sigma|_{P_\sigma}
   =\beta_\sigma|_{P_\sigma}
 \quad\text{at every type},
 \tag{18}
```

choose $`g_h\in G_o`$ agreeing with h on P. Define an observer O by


```math
O(h,q)=
 \begin{cases}
  q(bg_h^{-1}),&h\text{ is a root loop on the chart},\\
  q(\beta_*),&h\text{ is a root loop off the chart},\\
  q(1_V),&h:o\to V\text{ is an old-target arrow}.
 \end{cases}
 \tag{19}
```


Different extensions $`g_h`$ differ on the right by a member of $`G_o(P)`$, so the character invariance proves well-definedness. The profile is P-pinned. For $`\mu\in G_o`$, choose $`g_{\mu h}=\mu g_h`$; the first row then satisfies

```math
(\rho_\mu q)(bg_h^{-1}\mu^{-1})=q(bg_h^{-1}).
 \tag{20}
```

The off-chart row is invariant because $`\beta_*\mu=\beta_*`$. All old-target rows are identity rows. In fact the full transport of O to every old object is its whole identity observer, at every subsequent old future. This verifies landing even in an arbitrary higher Henkin domain.

Every row in (19) reads a typed-onto arrow or the identity. Boolean preservation follows directly. At an arbitrary source-loop row h and arbitrary $`F^{\sigma t}`$, write $`a_h`$ for the arrow read there. Then

```math
\begin{aligned}
 O_h(\forall x^\sigma Fx)
 &\Longleftrightarrow
   \forall y\in D_\sigma(\mathrm{target}a_h)\,
             F(a_h,y),\\
 \forall x\in D_\sigma(o)\,O_h(Fx)
 &\Longleftrightarrow
   \forall x\in D_\sigma(o)\,
             F(a_h,\rho_{a_h}x).
\end{aligned}
 \tag{21}
```

Onto transport identifies these conditions; the existential calculation is identical. At an old row the transported observer is the whole identity. Thus the comparison holds at every future row and every future input F, establishing the whole Q/P operation identities at all types. The equality clauses follow over C from Boolean preservation. O is fully logical for every finite list, and at the source it has current profile $`\chi_b`$.

If two admitted relations differ, they differ at an arrow h and some arbitrary target tuple. Match h on their finite pins by a selected b. On a complete-Henkin branch use a finite modification of the corresponding typed baseline; on a finite-pin branch match only the individual pin; on a self branch extend the finite typed partial permutation to a finite-support permutation. The same target tuple still distinguishes the two rows. Only now lift that tuple along the typed-onto b. The observer (19) distinguishes the two resulting current applications. This proves full typed OS.

The same match-then-lift argument proves current BF at every type directly: if a future row of a pinned F has a witness, match that row on its pin by an onto selected arrow and lift the witness. It never assumes that every finite-pin-branch arrow is onto.

If all components are complete-Henkin, every new arrow and every old arrow is onto at every type. BF therefore holds at all objects. Each old $`B_V`$ is externally complete, hence satisfies current $`BC_t`$; §5 supplies it at the source. This proves (2).

## 7 Failure of Actuality and simultaneous target theories

There is no true atom at the source. Given a true P-pinned proposition p, choose $`a\in C_e\setminus P_e`$. Define r to have self row

```math
r(h)=[\beta_e h_e(a)=\beta_e(a)]
```

and zero rows at all old objects. This profile is admitted and pinned by a. The proposition $`p\land r`$ is true at the identity. A root permutation fixing every name in P can move a to a different colour. At that row p remains true but r is false. Hence

```math
0<p\land r<p.
 \tag{22}
```

Thus (1) includes $`\neg\mathrm{Actuality}`$.

Every old pure sentence keeps its original truth because all old typed domains, operations, and outgoing arrows are unchanged. Since every old object is reached by at least one selected arrow, choosing any set-many permitted component witnesses makes their witnessed sentences simultaneously possible at o.

The complete-Henkin clause genuinely permits intensional target domains; no target Extensionality premise appears in its proof. The finite-proposition special case requires only all-type onto old transports. More generally the proof uses external completeness solely at proposition type and complete Boolean transport there, not at higher relational types.

The ordinary finite-pin clause permits combining these targets with the earlier C5 target where $`BC_t`$ fails and with finite-pin targets having nononto old arrows. Such combinations retain current (1), but (2) is not asserted for them.

This remains a scoped cover theorem, not a proof of $`\mathrm{Con}(C+\mathrm{Max}(C)+OS+BC_t)`$. No representation of arbitrary intensional Henkin C targets by the permitted classes is supplied. In particular, the necessary completeness in (2) prevents treating the complete-Henkin class alone as C-complete.

## 8 Arbitrary C targets and pure Maximalism

Here drop both the proposition-completeness and the onto-transport restrictions on the old components. Let $`\mathcal A`$ be any nonempty set-sized family of disjoint C action models, with arbitrary Henkin domains. Choose typed name sets of cardinality $`\kappa`$ dominating their old domains, and baseline interpretations onto every old domain with infinite fibres, as in §2.

### 8.1 The isolated interpretation root

First give the new source only its identity endomorphism. Add an arrow $`I:o\to V`$ for **every** typed interpretation of the auxiliary names in the domains at V, with no surjectivity requirement. Postcomposition by an arbitrary old arrow k is the transported interpretation kI, which is again allowed.

Use exactly the finite-name pinning and landing domains of the [original interpretation-root construction](../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/coalesced-pinned-interpretations-root.md). At the identity the current relation extension is unconstrained. At every old interpretation, its full future section must land in the old target domain. The finite pin condition concerns old interpretations, not the isolated identity.

The old proof of language closure applies: transported parameters depend on their finitely many pinned names; term evaluation at an old target is its own admitted Henkin denotation. At the identity the usual current extension is permitted. Thus this is a C model, and every old component is unchanged.

For a relational auxiliary name c, give $`\widehat c`$ its interpreted old rows and an empty identity row. Exactly as in (9),

```math
\rho_I\widehat c=I(c).
 \tag{23}
```

At individual type use the literal name. An interpretation b obtained by finitely modifying an onto infinite-fibre baseline remains onto at every name type. Equation (23) therefore makes its action onto at every actual type as well.

Such selected b approximate arbitrary old interpretations on every finite typed pin. They need not approximate their infinite ranges or commute with any old inverse: only agreement on the finitely many named parameters is used.

For a selected b define $`O_b`$ by

```math
O_b(1_o,q)=q(b),\qquad
 O_b(h,q)=q(1_V)\quad(h:o\to V\text{ old}).
 \tag{24}
```

Its identity row is allowed by the unconstrained current extension. Every old-target row is independent of the interpretation, so the observer is empty-pinned. Its whole transport into every old object is the identity operation, including at every subsequent old future; hence it lands in every old Henkin domain.

At the source identity, Boolean preservation is immediate and Q/P preservation follows by reindexing along the all-type onto b. At every old future, the observer is the whole identity. This checks each preservation identity at every future input, exactly as in (21), so $`O_b`$ is qualified at all types simultaneously. No onto assumption about old arrows is used.

For full typed separation, a distinction already at the source's current tuple is detected by the identity observer. Otherwise it occurs at an old interpretation I and an arbitrary target tuple. Match I on the pins of the two relations by a selected b, retain the same distinguishing tuple, and then lift that tuple along b using (23). The observer $`O_b`$ detects the distinction. This proves OS.

The same approximation and lift proves current $`BF_{\mathrm{all}}`$. It does not prove necessary BF: old counterexamples remain intact.

The root-only proposition, true at $`1_o`$ and false at every old arrow, is an admitted true atom. Thus Actuality holds. Moreover every external current relation on the actual typed domains is the current extension of an admitted relation: give it the chosen identity extension and zero old rows. Under the stated ZFC metatheory, this proves all-type Relational Choice directly by choosing a current witness for each input and representing its graph.

It also proves the exact [preorder form of all-type Zorn](../../classicism-results-2026-10-24-v2/source/topics/classicism/principles/zorn-r.yaml). Quotient a current admitted preorder by mutual comparability. For each chain in the quotient partial order, choose one representative per equivalence class. Its representative set is an antisymmetric chain for the original preorder and has an admitted current predicate. The internal premise therefore gives a bound for it, hence a bound for the quotient chain. External Zorn supplies a maximal quotient class. Any representative m satisfies the required conclusion: every element above m is also below m.

Consequently the isolated source satisfies


```math
C+OS+BF_{\mathrm{all}}
 +\mathrm{Actuality}
 +RC_{\mathrm{all}}+\mathrm{Zorn}_{\mathrm{all}},
 \tag{25}
```


while preserving every component. These are current principles. In particular, this argument does not necessitate its optional choice or maximality conclusions.

### 8.2 A permutation source without Actuality

Alternatively retain all typed root permutations from (4), but take the designated source symmetry group to be trivial. Use all typed interpretations into every old object, rather than just the uniform interpretations (5). Retain finite typed pinning and old landing. Composition is automatic even when old transports are not onto. This change is confined to the unrestricted construction; the nontrivial colour symmetry used for $`BC_t`$ in §§1–7 is unchanged.

The recursive source domains and named entities still satisfy the language-closure proof of §3, now with no source symmetry condition. Selected finite modifications of the baselines remain onto at every type by (23), as do all root permutations.

For any selected onto interpretation or root permutation b, define

```math
O_b(h,q)=
 \begin{cases}
 q(b),&h\text{ is a root loop},\\
 q(1_V),&h:o\to V\text{ is old}.
 \end{cases}
 \tag{25a}
```

This observer is empty-pinned. At every old object it lands as the whole identity. At every source self row it reads the same onto b, so the arbitrary-future-input calculation (21) proves whole Q/P preservation there. Boolean preservation is immediate. There is no chart or extension-choice issue because no designated symmetry must be respected. Matching a distinguishing old interpretation on its finite pins, then lifting its tuple, proves OS. Distinctions at self rows are read by root permutations, which are already typed-onto. The same finite-pin approximation proves current BF at all types.

Every external current relation R is admitted by giving it the same row R at every root loop and zero rows at every old object. This is empty-pinned and lands. It need not be invariant under root argument transports: application at h evaluates R on the transported arguments, exactly as the action-model semantics requires. The finite pins of those arguments ensure that application and abstraction retain finite pins. Hence current relational fullness, and the ZFC proofs of $`RC_{\mathrm{all}}`$ and $`\mathrm{Zorn}_{\mathrm{all}}`$ in §8.1, hold here too.

To refute Actuality, take a true P-pinned p and a fresh individual name $`a\notin P_e`$. Let r have self row $`r(h)=[h_e(a)=a]`$ and zero old rows. It is admitted with pin $`\{a\}`$. The proposition $`p\land r`$ is true at the identity. A root permutation fixing P but moving a leaves p true and makes r false. Thus $`0<p\land r<p`$, so no true proposition is an atom.

Thus the unrestricted permutation source satisfies


```math
C+OS+BF_{\mathrm{all}}+\neg\mathrm{Actuality}
 +RC_{\mathrm{all}}+\mathrm{Zorn}_{\mathrm{all}}.
 \tag{26}
```


No source Boolean-completeness claim follows from this unrestricted construction. The joins in §§4–5 used the target hypotheses explicitly; those hypotheses have now been dropped.

### 8.3 The exact Maximalism corollaries

For the component input, use the C-complete action-model family of the original interpretation-root construction: its “Components” clause supplies pointed action models witnessing every C-consistent sentence, and its “Maximalism holds” argument uses preservation of those witnesses. We use only the pure-language instance of that semantic input.

Concretely, the pure finitary language has a set of sentences. For each C-consistent pure sentence $`\varphi`$, take a pointed C action model in which $`\varphi`$ is true. The established action-model existence input and set-theoretic Collection and Choice give a set-sized family of these witnesses; make their objects and arrows disjoint. Choose $`\kappa`$ only after that family has been chosen. This does not assert that the restricted classes of §1 are C-complete.

In either unrestricted source, every witness object is reached by an interpretation arrow. No old outgoing arrow or domain has changed. Therefore every C-consistent pure $`\varphi`$ is possible at the source. This is pure $`\mathrm{Max}(C)`$, with consistency relative to the original fixed C, not to C+Ext or to a new semantic-class theory.

Applying §§8.1–8.2 to that family yields the two simultaneous models


```math
\begin{aligned}
 &C+\mathrm{Max}(C)+OS+BF_{\mathrm{all}}
   +\mathrm{Actuality}+RC_{\mathrm{all}}+\mathrm{Zorn}_{\mathrm{all}},\\
 &C+\mathrm{Max}(C)+OS+BF_{\mathrm{all}}
   +\neg\mathrm{Actuality}+RC_{\mathrm{all}}+\mathrm{Zorn}_{\mathrm{all}}.
\end{aligned}
 \tag{27}
```


The original human-authored interpretation-root construction is not altered by this note. Its named-entity, landing and preservation arguments are the input; the sufficiently large typed name supply and the wholly qualified observer constructions (24) and (25a) supply the new full-OS verification.

Neither line of (27) includes $`BC_t`$. The exact consistency question
$`\mathrm{Con}(C+\mathrm{Max}(C)+OS+BC_t)`$ remains unresolved.

## 9 Sources and verification

- **New construction and proof:** misc, this note, §§1–8; OpenAI Codex, 26 October 2026, unpaginated.
- **Mixed finite-pin predecessor:** [A complete observer source for mixed finite support and Henkin targets](mixed-finite-pin-henkin-completeness-cover.md), §§2–5, for the finite-pin lift, source symmetry, and reader chart.
- **Typed-name landing framework:** [Coalesced finitely pinned interpretation root](../../classicism-results-2026-10-24-v2/source/topics/classicism/writeups/coalesced-pinned-interpretations-root.md), “The construction,” “The entities $`\hat c`$,” and “It is a model of C.” The present uniform-interpretation and section-valued envelope arguments are new.
- **Ordinary finite-pin framework:** [Symmetric ideally-full models](../../classicism-results-2026-10-24-v2/source/topics/classicism/groups/symmetric-ideally-full.yaml), with its cited Definitions 15–18, Lemma 21 and Proposition 22.
- **Qualification and type scope:** [Logical observer separation and its hierarchy](../../classicism-results-2026-10-24-v2/proofs/logical-observer-hierarchy.md), §1.

The uniform factorization, named lifts, and complete-Boolean section joins and envelopes received independent conceptual checks from other OpenAI Codex agents.
