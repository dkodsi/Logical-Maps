# Finite colour patterns and propositional Boolean completeness

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new completeness, reflection and Zorn arguments: `misc`, this note, §§2–6, unpaginated. The existing symmetric model and its observer results retain the sources in §7.

Boolean Completeness at t does not turn ordinary logical separation into endpoint separation, even when C5, necessary reversible separation and necessary Boolean Completeness at t all hold. The existing two-colour finite-pinning model supplies the distinction. Its proposition algebra is atomless, but every admitted predicate's current extension has an actual Boolean least upper bound.

There is also a positive persistence theorem: over C5, ordinary logical separation makes each assumed Boolean Completeness instance necessary. The countermodel shows why this does not suffice to derive Actuality from the type-t instance. Completeness at higher relation types must not be silently substituted for propositional completeness.

## 1. The existing model and the exact completeness statement

Use exactly the model in [Finite colour patterns](finite-pinning-dedekind-propositions.md), §§2–4. There is one countably infinite object X, partitioned into two infinite colour classes A and B. Arrows are all bijections of X. The designated symmetry group is

$$
G=\mathrm{Sym}(A)\times\mathrm{Sym}(B).
\tag{1}
$$

At every relational type, the domain consists of the symmetric intensions pinned by some finite subset of X. Evaluation is at the identity arrow. The colour classes are external construction data, not additional nonlogical predicates. This is the symmetric ideally-full construction cited in §7.

For x∈X, write $q_x$ for the admitted proposition consisting of the arrows h for which h(x)∈A. A proposition pinned by a finite S is precisely a Boolean function of the finitely many tests $q_x$, x∈S. Every assignment of colours on a finite set is realized by an arrow: prescribe distinct images in the required infinite colour classes and extend the finite partial bijection. Consequently the proposition algebra is the free Boolean algebra on these tests, and its S-pinned subalgebra $B_S$ has

$$
|B_S|=2^{2^{|S|}}.
\tag{2}
$$

These are external descriptions of the already admitted propositions; no additional proposition or predicate is added to the model. Boolean order is inclusion of sets of arrows.

The [Boolean Completeness instance at t](../../source/topics/classicism/principles/boolean-completeness-t.yaml), in its equivalent least-upper-bound form, is

$$
\mathrm{BC}_t:
\forall Y^{tt}\,\exists u^t\,\forall z^t
\left[u\le z\ \leftrightarrow\
\forall b^t(Yb\to b\le z)\right].
\tag{3}
$$

Here Yb is current truth. It is not the assertion Yb=Top, and the family whose upper bound is requested is not automatically represented by the weighted formula ∃b(Yb∧b). We prove (3) for the actual current extension of every admitted Y.

## 2. Finite projection is the join of a stabilizer orbit

Fix finite P⊆X and an admitted proposition b with finite pin T. Define $\pi_Pb$ by existentially eliminating the Boolean coordinates in T∖P from the finite truth table of b. Equivalently, its value on a colour assignment on P is true exactly when that assignment extends to a colour assignment on P∪T making b true. This is a finite Boolean operation on truth tables, so $\pi_Pb$ belongs to $B_P$. It does not assert an internal existential quantifier over external assignments.

The construction is independent of the chosen pin T: $\pi_Pb$ is the least P-pinned Boolean upper bound of b. It has the elementary properties

$$
b\le\pi_Pb,
\qquad
\pi_P(gb)=\pi_Pb\quad(g\in G_{(P)}),
\tag{4}
$$

where $G_{(P)}$ fixes P pointwise and gb denotes transport of the proposition by g. On generators this transport sends $q_x$ to $q_{g(x)}$. In particular every member of b's $G_{(P)}$-orbit lies below $\pi_Pb$.

**Orbit-join lemma.** The proposition $\pi_Pb$ is the least upper bound, in the entire proposition algebra, of the $G_{(P)}$-orbit of b.

To prove minimality, let u be any upper bound of that orbit and choose a finite pin S for u. Suppose $\pi_Pb$≰u. A colour assignment on P∪S then makes $\pi_Pb$ true and u false. By the definition of $\pi_Pb$, its restriction to P extends to an assignment on P∪T making b true.

Choose g∈$G_{(P)}$ which moves every element of T∖P outside P∪S. Such a g exists because both original colour classes are infinite: choose fresh images in the same original class, then extend the finite partial permutations within A and B. The assignments just chosen can now be combined. Keep the assignment on P∪S, and give g(x), for x∈T∖P, the colour assigned to x in the assignment making b true. There is no conflict because g(T∖P) is disjoint from P∪S. All finite colour assignments are realized by arrows, so some arrow h makes gb true and u false. This contradicts gb≤u.

Thus $\pi_Pb$≤u. Together with (4), this proves the lemma. Only finite Boolean calculations and finite fresh-point choices were used; the orbit itself need not be an admitted indexed family.

## 3. Every admitted current family has an actual join

Let Y:tt be admitted and let P pin Y. Its current extension

$$
\mathcal F:=\{b\in D_t(X):Yb\text{ is true at the identity}\}
\tag{5}
$$

is invariant under $G_{(P)}$. This standard consequence of pinning and symmetry can be seen directly from the predicate's profile. For g∈$G_{(P)}$, symmetry identifies Y's truth on (id,b) with its truth on (g,gb); P-pinning identifies the latter with its truth on (id,gb). Hence b∈ℱ iff gb∈ℱ.

There are only finitely many different values $\pi_Pb$, because they all belong to the finite algebra $B_P$. Let u be their finite Boolean join:

$$
u:=\bigvee\{\pi_Pb:b\in\mathcal F\}\in B_P.
\tag{6}
$$

If ℱ is empty, take u=Bottom. The finite set in (6) is used externally to establish existence of an element of the semantic domain. No admitted enumeration of ℱ, uniform selector in Y, or internal finiteness of all propositions is claimed.

Every b∈ℱ lies below $\pi_Pb$ and therefore below u. Conversely, if z bounds ℱ, invariance makes z an upper bound of the entire $G_{(P)}$-orbit of each b∈ℱ. The orbit-join lemma gives $\pi_Pb$≤z for each b, and the finite join gives u≤z. Thus u is the actual least upper bound of ℱ. This proves (3), and Boolean complementation gives its recorded greatest-lower-bound form.

The same pure sentence is true at every future evaluation: there is only one object, and each future truth clause evaluates that closed sentence at that object. Equivalently, naturality of closed pure interpretations makes its proposition constant on the arrows. Therefore this unchanged model satisfies

$$
\boxed{\Box\mathrm{BC}_t.}
\tag{7}
$$

This proof is specific to the finite colour-pattern algebra and the fresh-support action. External finiteness of each $B_P$ by itself was sufficient for the injection theorem in the earlier note; it is not being asserted sufficient for (7) in an arbitrary symmetric model.

## 4. The observer and Actuality boundary

The existing model theorem gives C5, full reversible logical separation and its separately boxed instances. All type transports are bijective. The earlier finite-pin argument also gives the internal sentence $D_t$ that every admitted injective proposition operation is onto.

The proposition algebra is atomless: for a nonzero b with finite pin T, a fresh coordinate $q_x$ splits b into two nonzero parts. Consequently Actuality is false. Indeed, a true proposition entailing every truth would be a Boolean atom: for any p, either p or ¬p is true, so that proposition lies below one side of every Boolean partition. Endpoint separation is false as well, since it entails propositional atomicity.

Combining these already established facts with (7), the model satisfies

$$
\boxed{
\mathrm{C5}+\Box\mathrm{Rev}+\Box\mathrm{BC}_t
 +D_t+\text{atomless propositions}
 +\neg\mathrm{Actuality}+\neg\mathrm{End}.}
\tag{8}
$$

The boxed observer statement is a schema of its separately boxed finite-list, relational-output instances. It is not an infinitary conjunction in the language.

In particular, C5+OS+$\mathrm{BC}_t$ does not imply Actuality or endpoint separation, even if OS is strengthened to ☐Rev and $\mathrm{BC}_t$ is made necessary. The stronger completeness required by the usual Actuality argument already occurs at tt, the type of proposition operations.

**Exact higher-type specialization.** Over C5,

$$
\mathrm{BC}_{tt}
\quad\Longrightarrow\quad
\mathrm{Plen}_{t,t}
\quad\Longrightarrow\quad
\mathrm{Actuality}.
\tag{8a}
$$

For the first implication, specialize the proof of Bacon and Dorr's Proposition 2.14 to operations with proposition inputs and outputs. Given an admitted currently functional relation U:ttt, consider the admitted family of operations H:tt satisfying

$$
\forall x,p\,[U[x,p]\to Hx\le p].
\tag{8b}
$$

Take its actual least upper bound G at type tt, supplied by $\mathrm{BC}_{tt}$. Fix an input a and its unique U-output p. The admitted spike H₀(x):=(x=a)∧p belongs to (8b): when x=a, uniqueness gives the specified output p, while when x≠a, C5 makes x=a identical to Bottom. Thus H₀≤G, and evaluation at a gives p≤Ga.

The admitted cap H₁(x):=(x≠a)∨p bounds every operation in (8b). At x=a this follows from U[a,p]; at x≠a the cap is Top. These pointwise algebraic inequalities give the order inequality between whole operations by BF_t: each input inequality is a necessary implication, and BF_t collects them into the necessary universal implication defining that order. C5 supplies BF_t. Hence G≤H₁ and Ga≤p. Antisymmetry gives Ga=p. Since a was arbitrary, G represents the functional relation U, proving precisely $\mathrm{Plen}_{t,t}$. No completeness at any further type or uniform choice of G across relations is used.

For the second implication, apply $\mathrm{Plen}_{t,t}$ to the functional relation whose output is p when p is true and Top when p is false. Its admitted representing operation Z has every Zp true, and Zp=p for true p. Then a:=∀p Zp is true and lies below every true p by universal instantiation. It witnesses Actuality. This is the type-t proof of Proposition 2.15, as detailed in [the Plenitude bridge](plenitude-endpoint-bridge.md), §2.

Thus the present model satisfies $\mathrm{BC}_t$ but fails $\mathrm{BC}_{tt}$, with the former necessary. Under C5+OS, $\mathrm{BC}_{tt}$ reaches End through Actuality and the established atomic-observer converse; $\mathrm{BC}_t$ does not. The published proofs supply the underlying implications in (8a); the explicit restriction to these exact type instances is the specialization recorded here.

Section 6 will also refute $\mathrm{Zorn}_t$ in this model. Thus it does not refute an implication with $\mathrm{BC}_t$ and $\mathrm{Zorn}_t$ both added. The model already satisfies Rev, so it does not separate InjSep from SplitMono or settle OS+$J_t$⇒Rev∨$K_t$.

## 5. Logical separation reflects completeness into necessity

There is a general positive complement to (8). Work over C5, fix an admitted relational type σ, and let Δ contain σ and σt. Assume propositional separation by $\mathrm{Good}_\Delta$ observers. Then

$$
\boxed{
S_{t,\Delta}+\mathrm{BC}_\sigma
\quad\Longrightarrow\quad
\Box\mathrm{BC}_\sigma.}
\tag{9}
$$

All additional premises in (9) are current. In particular neither $\mathrm{BC}_\sigma$ nor separation is assumed necessary.

For the proof, use the greatest-lower-bound definition

$$
\mathrm{GLB}_\sigma(y,Y):=
\forall z^\sigma\left[
 \bigl(\forall r^\sigma(Yr\to z\le r)\bigr)
 \leftrightarrow z\le y\right].
\tag{10}
$$

The algebraic order judgments in (10) are identities of relation objects. Under C5 every such identity proposition is an endpoint; a Boolean observer fixes it. Its full quantifier and Boolean identities therefore give, for every admitted $\mathrm{Good}_\Delta$ observer E,

$$
E\bigl(\mathrm{GLB}_\sigma(y,Y)\bigr)
=\mathrm{GLB}_\sigma(y,\lambda r.E(Yr)),
\tag{11}
$$

and hence

$$
E(\mathrm{BC}_\sigma)
=\forall Y^{\sigma t}\,\exists y^\sigma\,
 \mathrm{GLB}_\sigma(y,\lambda r.E(Yr)).
\tag{12}
$$

For each Y the composite λr.E(Yr) is admitted. Current $\mathrm{BC}_\sigma$ applied to that composite makes the right side of (12) true. Thus every eligible E accepts $\mathrm{BC}_\sigma$. It also accepts Top, so propositional separation gives $\mathrm{BC}_\sigma$=Top, which is exactly (9). No optional hypothesis has been necessitated.

For σ=t, the direct proof uses Δ={t,tt}. The established C5 theorem that each $\mathrm{Good}_{\{t\}}$ observer preserves every finite requested quantifier list permits the single separation instance $S_{t,\{t\}}$ instead. Consequently C5+OS reflects $\mathrm{BC}_t$, and indeed every assumed $\mathrm{BC}_\sigma$ instance, into necessity. This is a persistence theorem, not a type-lifting theorem from $\mathrm{BC}_t$ to $\mathrm{BC}_r$, as the model in §4 demonstrates.

## 6. An admitted preorder refutes Zorn at t

The failure concerns exactly the σ=t instance of the [recorded preorder Zorn principle](../../source/topics/classicism/principles/zorn-r.yaml). Its chains are admitted predicates on propositions, and TotalOrder includes antisymmetry on the current members.

For an external finite subset F⊆A, put $q_F$:=∨_{x∈F}$q_x$, with $q_\varnothing$=Bottom. Independence of the colour coordinates gives

$$
q_F\le q_H\quad\longleftrightarrow\quad F\subseteq H.
\tag{13}
$$

Let V be the external current subset consisting of exactly these $q_F$. It is invariant under G, since $gq_F=q_{g(F)}$ and g preserves A. The unary profile

$$
\widehat V(h,p):\longleftrightarrow p\in V
\tag{14}
$$

is independent of the arrow h, hence empty-pinned, and is symmetric under the simultaneous target-group action. It is therefore an admitted predicate in the specified ideally-full model. Define a two-input profile in the same way from

$$
P(b,c):\longleftrightarrow
b\notin V\ \text{or}\ (c\in V\text{ and }b\le c).
\tag{15}
$$

This profile too is empty-pinned and symmetric, since both V and Boolean order are G-invariant. Currying does not introduce an admission problem: fixing a proposition b with pin S gives the section (h,c)↦P(ρ_t(h)b,c). Arrows agreeing on S have identical transported b objects, so this section is S-pinned; simultaneous G-invariance supplies its symmetry. Thus P is an actual admitted relation of type ttt, not merely an external order used in the proof.

At the current point, (15) is a preorder. Invalid elements lie below everything; valid elements are ordered by inclusion of their finite coordinate sets. It has no maximal element. An invalid b lies strictly below the valid Bottom. A valid $q_F$ lies strictly below $q_{F\cup\{x\}}$ for any x∈A∖F, which exists because A is infinite.

Nevertheless every admitted current chain has an upper bound. Let Y:tt be such a chain and choose a finite pin N for it. Its current extension is invariant under $G_{(N)}$, as in §3. Every finite-order g∈$G_{(N)}$ acts on that extension as an order automorphism of its antisymmetric total order. Such an automorphism fixes every member: if b and gb were unequal, totality would orient them strictly, and iterating that inequality around the finite cycle would contradict antisymmetry.

Suppose a valid $q_F$ belongs to the chain. If F contained x∈A∖N, choose y∈A∖(F∪N). The transposition of x and y belongs to $G_{(N)}$ and has order two, but moves $q_F$ to a different proposition by (13). This contradicts the preceding fixed-point conclusion. Hence every valid chain member has F⊆N∩A and lies below $q_{N\cap A}$. Every invalid chain member lies below that same valid proposition by (15). Thus $q_{N\cap A}$ is an admitted upper bound for the entire current chain, including an empty chain or a chain containing an invalid member.

The premise of $\mathrm{Zorn}_t$ is true for this admitted preorder, while its conclusion is false. Therefore the model additionally satisfies

$$
\boxed{\neg\mathrm{Zorn}_t.}
\tag{16}
$$

Only the chain's actual antisymmetry, the finite pin and finite-order symmetries were used. No external finiteness of the whole proposition domain, admitted enumeration of V, or uniform choice of chain bounds was assumed. The failure locates the missing extra premise in the controlled-transversal theorem; it supplies no conclusion about C5+OS+$\mathrm{BC}_t$+$\mathrm{Zorn}_t$.

## 7. Sources

The orbit-join, actual-current-completeness, observer-reflection and Zorn countermodel arguments are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, direct source `misc`, §§2–6 of this note, unpaginated. No published source is being credited with these new verdicts.

The exact semantic construction, finite colour-pattern algebra, atomlessness, $D_t$ and reversible separation are in [Finite colour patterns](finite-pinning-dedekind-propositions.md), §§2–6. Its construction sources are Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8, §3.1, p. 9, and Lemma 21, p. 10; and Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, pp. 73–79. See also the recorded [symmetric ideally-full model framework](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). These sources supply the framework, not the new completeness theorem.

The distinction between $\mathrm{BC}_t$ and $\mathrm{BC}_{tt}$ uses [the exact recorded $\mathrm{BC}_t$ statement](../../source/topics/classicism/principles/boolean-completeness-t.yaml), the proof of [C5 plus completeness implies Plenitude](../../source/topics/classicism/results/c5-and-completeness-imply-plenitude.yaml), and [the Plenitude bridge](plenitude-endpoint-bridge.md), §2. The underlying published arguments are Bacon and Dorr, *Classicism*, draft of 16 May 2023, Propositions 2.14–2.15, pp. 32–33. Their exact type-localization in (8a) is displayed here; it is not claimed to be a separate existing database arrow. The same-list to all-type qualification reduction used after (12) is [Modal selectors and quantifier reduction](../modal-selectors-and-quantifier-reduction.md), §4.
