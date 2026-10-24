# Linear and circular fibre orders: necessary separation without qualified left inverses

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the construction and new verdicts: `misc`, this note, §§1–9, unpaginated. The underlying symmetric-model framework and earlier observer theorems are attributed in §10.

This two-object model satisfies C5 and necessary full ordinary logical separation, but fails qualified left-inverse separation. Its finite-pin proposition algebras are finite, so every admitted injective proposition operation is onto. Consequently left-inverse separation and reversible separation coincide in this model. Their failure is proved by a closed pure sentence, rather than inferred from a failure of a symmetry-conjugacy criterion.

The model proves

$$
\mathrm{C5}+\Box\mathrm{OS}\ \not\Longrightarrow\ \mathrm{SplitMono}.
\tag{1}
$$
All positive separation claims have full relational output scope, every finite external qualification list and full composite preservation identities. Section 9 identifies one precise finite-list propositional instance which fails.

## 1. The two symmetry groups and the model

Let L be the rational line with its usual order. On another copy D of the same set put the circular-order relation induced by that linear order:

$$
C(x,y,z)\quad\Longleftrightarrow\quad
x<y<z\ \lor\ y<z<x\ \lor\ z<x<y.
\tag{2}
$$
This is a countable dense circular order. Its open arcs between any two distinct points, with their induced linear orders, are countable dense linear orders without endpoints.

Take the individual sets

$$
W=L\times\mathbb N,\qquad V=D\times\mathbb N.
$$
The sets $B_q=\{q\}\times\mathbb N$ are the original fibres at either object. Define G at W to consist of all permutations inducing an order automorphism of L on the fibres and an arbitrary bijection within each fibre. Define H at V in the same way, with a circular-order automorphism of D on the fibres. In particular both groups contain every permutation of a single fibre, extended by identity outside it.

Use W and V as the objects of the symmetric ideally-full action construction. Arrows between each ordered pair of objects are **all bijections**. At every relational type, the domain consists of exactly the symmetric intensions pinned by a finite subset of the source object. Individuals are the stated underlying sets, with the arrow action. Evaluation at either object is at its identity arrow. If a signature expansion is wanted, every nonlogical relational constant may denote the top element of its type.

The cited construction makes this a model of C. Since every arrow has an inverse, every induced type action is bijective. Thus C5, all Barcan instances and Functionality hold at both objects and throughout their future evaluations. Arrows and symmetry groups are external model data, not functions of a forbidden individual-output type in the object language.

## 2. Current-relation admission and invariance

We use the following explicit admission fact. At an object X with designated group K, let R be an external relation on a finite tuple of current admitted domains. Suppose R is invariant under K_(S), the subgroup fixing a finite S⊆X pointwise. Then R is the current extension of an admitted relation.

To construct it, at an arrow h:X→Y and tuple u at Y, declare its profile true exactly when

$$
Y=X,\quad h|_S=g|_S\text{ for some }g\in K,
\quad R(\rho(g^{-1})u).
\tag{3}
$$
It is false outside this branch. If g′=gv is another witness, then v∈K_(S), so invariance of R makes the answer independent of the witness. The branch and answer are S-pinned. For μ∈K, replacing h,u,g by μh,ρ(μ)u,μg preserves the answer. At any other target it remains false. Thus the profile is symmetric and finitely pinned, so ideal fullness admits it. At the identity choose g=id, giving exactly R as current extension.

Conversely, the current extension of an admitted relation pinned by S is invariant under K_(S). Symmetry compares its value at the identity tuple u with its value at g and ρ(g)u; pinning compares the latter value with the value at the identity and ρ(g)u. This argument uses designated symmetries g, not arbitrary arrows.

For an individual fibre B and b∈B, its current subset is invariant under K_({b}), since any such symmetry preserves the fibre of b. Formula (3) therefore supplies an admitted property with current extension B. This does not claim a uniformly chosen family of these properties.

## 3. Local symmetry comparisons in both directions

There is a bijection j:W→V with

$$
jGj^{-1}\subseteq H.
\tag{4}
$$
Identify the two copies of the rational coordinate and use identity on each fibre. An increasing bijection of the line preserves (2), so (4) follows.

For the reverse comparison choose two distinct circular quotient points c₀,c₁ and one individual a_i in each corresponding fibre. Put T={a₀,a₁}. The quotient action of H_(T) fixes c₀,c₁ and preserves each of the two open arcs between them. Choose order isomorphisms from those arcs onto L_{<0} and L_{>0}, respectively, and map each arc fibre bijectively to its corresponding target fibre. Map the two exceptional source fibres together bijectively onto the single target fibre B₀; for example use the even and odd positions in B₀ for the two source fibres. This defines a bijection b:V→W.

A member of H_(T) acts by an increasing bijection on each arc, keeps each exceptional fibre setwise and fixes the two pinned individuals. Its b-conjugate therefore preserves the linear order of all target fibres, fixes the fibre B₀ setwise and acts there by a permitted within-fibre permutation. Hence

$$
bH_{(T)}b^{-1}\subseteq G.
\tag{5}
$$
The packing of two infinite fibres into one is essential. Equations (4) and (5) are not global conjugate inclusions in both directions: the reverse one uses a nonempty finite stabilizer.

## 4. Full ordinary observers and their necessary separation

For completeness, here is the observer supplied by a local inclusion. Suppose c:X→Y and finite S⊆X satisfy

$$
cK_{X,(S)}c^{-1}\subseteq K_Y.
\tag{6}
$$
For h:X→Z and a proposition q at Z define E(h,q) by

$$
E(h,q)\quad\Longleftrightarrow\quad
\begin{cases}
cg^{-1}\in q,& Z=X\text{ and }h|_S=g|_S\text{ for some }g\in K_X,\\
\mathrm{id}_Z\in q,&\text{otherwise}.
\end{cases}
\tag{7}
$$
In the first branch, replacing g by gv with v∈K_{X,(S)} changes cg^{-1} by left multiplication with cv^{-1}c^{-1}∈K_Y. Proposition symmetry makes membership unchanged. Thus (7) is well defined. It is S-pinned. For target symmetry μ∈K_X, use the representative μg and the transport law

$$
k\in\rho_t(\mu)q\quad\Longleftrightarrow\quad k\mu\in q.
$$
The first branch is invariant. Its complement is invariant as well; there the identity observation is unchanged in truth because q is symmetric under its target group. Ideal fullness therefore supplies an admitted E:tt. At the identity its truth profile is evaluation at c.

Every branch observes at a bijective arrow; write a_h for that arrow, with representatives chosen only for the calculation. For an arbitrary future arrow r:X→Z, input q at Z and further coordinate l:Z→U, application and transport give

$$
l\in(\rho_{tt}(r)E)(q)
\quad\Longleftrightarrow\quad a_{lr}l\in q.
\tag{8}
$$
Boolean operations are the corresponding set operations, so (8) preserves them and both endpoints. For a quantifier at any admitted type σ, compare the two sides of its commutation law at r and l. One quantifies over the whole σ-domain at the target of a_{lr}; the other quantifies over the images under ρ_σ(a_{lr}) of the σ-domain at U. They agree because this type action is onto, with the inverse arrow supplying its inverse. The existential calculation is the same. These checks hold at every future r and all inputs there, so they establish full composite identities, not only current truth commutation. The translated equality clauses follow from Boolean qualification over C; alternatively equality judgments are endpoints because all type actions are injective. Thus E is Good_Δ for every requested finite Δ.

Now let d be any nonbottom proposition at X, pinned by finite P, and choose h:X→Y in d. For this ordered pair of objects choose the comparison c₀:X→Y supplied by identity, (4), or (5), with its finite stabilizer pin S₀. Extend the finite partial bijection (c₀^{-1}h)|P to a finite-support permutation π of X. Put c=c₀π and choose finite

$$
S\supseteq P\cup S_0\cup\mathrm{supp}(\pi).
$$
Every member of K_{X,(S)} commutes with π. Consequently c still satisfies (6). It agrees with h on P, so c∈d. The admitted observer (7) therefore makes Ed true at X.

Apply this to Boolean symmetric differences to separate any two distinct propositions. Functionality lifts separation to every relational output type. The construction works at W and V, for every finite qualification list. Each closed separation instance is therefore true at every future object, yielding the separately boxed schema

$$
\mathrm{OS}\quad\text{and}\quad\Box\mathrm{OS}
\tag{9}
$$
at both objects. No infinite qualification or common observer across all instances is asserted.

## 5. Finite-pin proposition algebras and admitted injections

Fix a finite pin S at either source object. For a fixed target, the orbit of an injective restriction h|S under its designated group is determined by finitely much data: which points have images in the same fibre, and the linear or circular order of the finitely many image fibres. These data are complete orbit invariants, since the quotient finite order isomorphism extends and within-fibre finite injections can be matched by permutations. There are finitely many possibilities.

A symmetric S-pinned proposition is determined, at each of the two targets, by which of these finitely many orbits it accepts. Hence the algebra B_S of S-pinned propositions is finite. This is external finiteness of each fixed-pin algebra, not a finite enumeration of the entire proposition domain.

By [Finite colour patterns](finite-pinning-dedekind-propositions.md), §2, application respects the union of pins: if P pins E and S⊇P pins p, then S pins E(p). Its proof checks that for h,h′ agreeing on S, the transported inputs ρ_t(h)p and ρ_t(h′)p agree at every further arrow l, since lh and lh′ agree on S. Thus any admitted injective E restricts to an injective self-map of each finite B_S once S contains its pin. This map is onto B_S. Taking S also to contain a pin for an arbitrary q proves the internal sentence

$$
\mathsf D_t:=\forall E^{tt}\left[
 (\forall p,q\,[Ep=Eq\to p=q])
 \to\forall q\,\exists p\,[Ep=q]\right].
\tag{10}
$$
Current Functionality and (10) turn every admitted whole left inverse F∘E=I into a whole right inverse E∘F=I. When E,F are Good_Δ, the same witnesses remain qualified. Therefore SplitMono_Δ and Rev_Δ coincide here for each finite Δ, and so do their separation sentences at each output type. This is the finite-pin theorem, not an appeal to internal Frege finiteness.

The proposition algebras are also atomless. Given nonbottom p pinned by S and containing h:X→Y, choose distinct x,y outside S. The property of arrows to Y whose x,y images lie in the same original Y-fibre is symmetric and pinned by {x,y}, and false at the other target, so it is admitted. There are bijections agreeing with h on S and sending x,y respectively into one common fibre or two different fibres. Both remain in p. This admitted property therefore splits p into two nonbottom parts.

## 6. Internal finiteness and the pure distinguishing sentence

Use the exact Frege definitions from [Background](../../source/topics/classicism/background.md). Put ν=(et)t,

$$
\begin{aligned}
\mathbf 0&:=\lambda X^{et}.\,\forall x^e\neg Xx,\\
\mathrm{Suc}(Z)&:=\lambda X^{et}.\,
 \exists y^e\,[Xy\land Z(\lambda u^e.\,Xu\land u\ne y)],\\
\mathrm{FiniteCardinality}(Z)&:=
 \forall U^{\nu t}\bigl[(U\mathbf0\land
 \forall Y^\nu[UY\to U(\mathrm{Suc}Y)])\to UZ\bigr],\\
\mathrm{Fin}(X)&:=\exists Z^\nu\,
 [\mathrm{FiniteCardinality}(Z)\land ZX].
\end{aligned}
\tag{11}
$$
At either object, Fin(X) holds exactly when X has an externally finite current extension. Here is the admission justification for that claim. For each standard natural number n, the pure numeral term Suc^n(0) has current truth extension exactly the properties with n instances; this follows by finite external induction directly from the first two lines of (11), using the exact admitted deletion abstract. Let N be the external set of current ν-objects **object-equal** to one of those standard numeral terms.

N is invariant under the designated group because each numeral is a closed pure term and is fixed by its action. The current-relation admission lemma of §2 with empty pin therefore supplies an admitted U whose current extension is N. U contains zero and is closed under Suc by equality substitution: the successor of the n-th numeral is the (n+1)-st. The induction clause in (11) implies that every internally finite cardinality is equal to a standard numeral. If it holds of X, X consequently has exactly n current instances for some standard n. Conversely a property with n current instances satisfies the n-th numeral, which is internally finite by n applications of the successor induction theorem. This proves the asserted standardness, without replacing coextension by identity or assuming that an external infinite set is automatically internally infinite.

For an admitted individual property X define

$$
\mathrm{Amor}(X):=
 \neg\mathrm{Fin}(X)\land
 \forall Y^{et}\bigl[Y\subseteq X\to
 (\mathrm{Fin}(Y)\lor
 \mathrm{Fin}(\lambda x.\,Xx\land\neg Yx))\bigr].
\tag{12}
$$
Thus X is infinite, and each admitted subset is finite or cofinite in it. The standardness just proved applies to every property in (12), including the displayed difference abstract.

Let P be the following **closed pure sentence**. There is an admitted total preorder R:eet such that, writing

$$
x\sim_R y:\!\!\Longleftrightarrow R(x,y)\land R(y,x),
\qquad
x\prec_R y:\!\!\Longleftrightarrow R(x,y)\land\neg R(y,x),
$$
every cell $\lambda y.\,x\sim_R y$ is Amor, and the quotient strict order is dense with no endpoints:

$$
\begin{aligned}
&\forall x,y\,[x\prec_R y\to
 \exists z\,(x\prec_R z\land z\prec_R y)],\\
&\forall x\,\exists y,z\,[y\prec_R x\land x\prec_R z].
\end{aligned}
\tag{13}
$$
This uses only individual arguments and relational outputs. There is no quotient type or external family in P. A total preorder and (13) describe the order of its actual equivalence classes; (12) is imposed through their admitted lambda-defined properties.

## 7. P holds at the linear object

The original fibre preorder, comparing rational coordinates by ≤, is G-invariant. Section 2 admits a relation having it as current extension. Its quotient is the rational line, so the required preorder and (13) hold.

Each original fibre B is infinite and amorphous. Given any admitted individual property Y, choose a finite pin N for it. Its current extension is invariant under G_(N), which contains every permutation of $B\setminus N$. Thus Y is constant on $B\setminus N$. If Y⊆B, it is either finite or cofinite in B. By §6 these are exactly the internal finiteness assertions in (12). The actual cells of the admitted preorder have these same current extensions, so they are Amor. Hence P is true at W.

## 8. P fails at the circular object

Suppose an admitted R witnessed P at V. Choose a finite pin N for R and enlarge it to meet at least one original fibre. Its current preorder and equivalence relation are invariant under H_(N). For each original fibre B write $T_B=B\setminus N$. This is infinite, and H_(N) contains the full group Sym(T_B), acting identically outside T_B.

**Each tail lies in one R-cell.** Choose x∈T_B and let D be its R-cell. D is infinite. If D contains a second point z of T_B, then for any y∈T_B a permutation of T_B fixing x and sending z to y shows x∼_R y. Thus T_B⊆D. If instead x is the only point of T_B in D, infinitude supplies z∈D outside T_B. A permutation of T_B sending x to an arbitrary y fixes z, so invariance gives y∼_R z. Again T_B⊆D, contrary to the assumed singleton intersection. This proves the assertion for every B; it also treats a cell initially meeting a tail in only one point.

**Different tails lie in different cells.** Suppose D contained T_B and T_{B′} for distinct original fibres. Section 2 supplies an admitted property with current extension B. Intersect it with the admitted cell property D. This yields an admitted subset of D whose extension contains T_B and whose complement in D contains T_{B′}. Both are externally infinite and hence internally infinite by §6, contradicting Amor(D).

**Every cell contains a tail.** Every individual outside N belongs to some T_B, and hence its entire tail belongs to its cell by the first assertion. A cell containing no tail would therefore be contained in the finite set N. It would be internally finite, again contrary to Amor.

Consequently the assignment B↦the cell containing T_B is an H_(N)-equivariant bijection between original fibres and R-cells. Each cell consists of its unique entire tail and possibly some of the finitely many points in N. No extra finite cells or unaccounted infinite cells remain.

Let k≥1 be the number of original fibres meeting N. The quotient action of H_(N) fixes exactly these k fibres. On all other fibres it has exactly k orbits: the open circular arcs between consecutive pinned quotient points. Each is nonempty and transitive, and every quotient automorphism fixing those k points lifts to H_(N), choosing within-fibre bijections which fix the finitely many pinned individuals. Via the equivariant bijection, the action on R-cells has exactly k fixed cells and k remaining orbits.

But R's quotient is a dense linear order without endpoints, preserved by H_(N). Arrange its k fixed cells in their R-order. The two outer gaps and the k−1 intervening gaps are k+1 nonempty invariant sets. They contain no fixed cell, and each must contain at least one of the remaining orbits. Disjointness would require at least k+1 such orbits, whereas there are only k. This contradiction proves that P is false at V.

## 9. The failed inverse-separation instance

The pure sentence P is true at W and false at V, and there are arrows in both directions. Therefore No Pure Contingency fails at both objects: use P at W and ¬P at V. The established theorem [Reversible separation implies No Pure Contingency](reversible-separation-and-pure-truth.md) refutes full Rev at both objects. Section 5 then refutes full SplitMono as well. Together with (9), this proves the non-implication (1).

There is also a precise finite-list failure. Expanding (11)–(13), all bound types in P belong to

$$
\Delta_0=\{t,e,et,eet,(et)t,((et)t)t\}.
\tag{14}
$$
The harmless t entry includes the endpoint notation and permits the existing same-list inverse patch. In C5 the term-conjugation proof of No Pure Contingency shows that every Good_Δ₀ involution fixes P. At W, P and Top are distinct proposition objects but both are true; every such involution gives them the same current truth. At V use ¬P and Top. Thus propositional involutive separation fails at this list at both objects. The same-list equivalence of reversible and involutive separation over C5 then refutes the propositional Rev instance for Δ₀. Finally (10) and Functionality make the qualified SplitMono and Rev classes identical for this same list, so that precise SplitMono instance fails too.

This does not assert failure at every qualification list. It supplies one explicit finite instance sufficient to refute the full schema. The model also has atomless propositions, as proved in §5, consistently with the earlier C5+necessary-OS+one-atom collapse theorem.

## 10. Sources

The linear/circular fibre construction, local comparison (5), finite-pin analysis, pure sentence P, internal-finiteness argument and inverse-separation obstruction are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–9, unpaginated.

The semantic construction is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, as recorded in [Symmetric ideally-full models](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). Its underlying action framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. These sources provide the model framework, not the new countermodel verdict.

The one-way arrow-evaluation observer is the construction in [Atomic observers and finite stabilizers](../operator-representation.md), §§4–6, direct source `misc`; its admission and full identities are repeated in §4. The current-relation admission lemma is also proved in [Finite-block symmetry](finite-block-symmetry-reversible-gap.md), §4. The finite-pin injection theorem is [Finite colour patterns](finite-pinning-dedekind-propositions.md), §§1–2, direct source `misc`.

The negative observer step uses [Reversible separation and pure truth](reversible-separation-and-pure-truth.md), §§2–5, and the same-list involution equivalence from [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §4. Frege zero, successor and finite cardinality are the exact definitions in [Background](../../source/topics/classicism/background.md); the semantic standardness needed here is proved in §6 rather than borrowed from an external finiteness assumption.

 No implication is inferred merely from a failed construction or from nonconjugacy of stabilizers.
