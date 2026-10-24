# Group identities for every reversible observer

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–6, unpaginated.

Any fixed nontrivial group-word identity, imposed on every tuple of reversible logical observers, forces a finite proposition domain when combined with reversible separation. Its exact strength is determined by the largest finite symmetric group satisfying that word. Conversely the corresponding finite Boolean algebra bound suffices.

The finite obstruction is proved directly, without invoking residual finiteness of free groups. A reduced word of length L acts nontrivially on an explicitly constructed set of L+1 vertices. A separate admitted patching construction embeds any finite symmetric group whenever sufficiently many disjoint nonzero propositions exist. All numerical bounds and words are fixed in the metalanguage; the object language gains no group type, word quantifier or arithmetic iteration operator.

## 1. Word syntax and a finite sentence with inverse witnesses

Fix variables x₁,…,x_r and a nonempty reduced word w in these variables and their formal inverses. Record its letters in application order:

$$
w=a_L\cdots a_1,
\qquad a_j=x_{i_j}^{\varepsilon_j},
\qquad \varepsilon_j\in\{1,-1\},
\qquad L\ge1.
\tag{1}
$$

Thus a₁ acts first. Reduced means that no adjacent a_{j+1},a_j are formal inverses. Products of operations and permutations use functional composition: fg means f∘g, with g acting first. This convention is retained throughout the finite permutation argument.

$\mathrm{Good}_{\{t\}}$ denotes the full established logical qualification over H, including its translated equality clauses and whole Boolean/type-t quantifier identities. We do not replace that H definition by a reduced package. Once C has been recovered, the redundant equality clauses may be dropped using the established Boolean-preservation theorem.

For admitted G,H:tt put

$$
\mathrm{Pair}(G,H):=
\mathrm{Good}_{\{t\}}(G)\land
\mathrm{Good}_{\{t\}}(H)\land
G\circ H=I\land H\circ G=I,
\qquad I:=\lambda p.p.
\tag{2}
$$

Define the whole unary operation W_w(G₁,H₁,…,G_r,H_r) by replacing a positive letter x_i with G_i, a negative letter x_i⁻¹ with H_i, and composing in the order (1). The required object-language sentence is

$$
\mathrm{Law}_w:=
\forall G_1H_1\cdots G_rH_r\,
\left[
\bigwedge_{i=1}^{r}\mathrm{Pair}(G_i,H_i)
\ \to\ W_w(G_1,H_1,\ldots,G_r,H_r)=I
\right].
\tag{3}
$$

Every equality in (2)–(3) is identity of complete operations. This is one finite formula for the fixed word. It ranges over all admitted qualified inverse pairs, rather than a chosen separating family or an external group of maps. Admitted whole inverses are unique by the usual composition calculation, so (3) expresses the expected group law without requiring an inverse-selection operation or Choice.

Full Rev retains its relational-output/finite-qualification-list schema meaning. It implies C5. Under C5, a $\mathrm{Good}_{\{t\}}$ observer and its admitted qualified inverse satisfy every requested finite quantifier list by the [same-observer type reduction](../modal-selectors-and-quantifier-reduction.md), §4. This is why the one finite list in (2) is sufficient for the theorem below.

For fixed external N≥1, let

$$
\mathrm{AtMost}_N(t):=
\exists u_1\cdots u_N\ \forall p\,
(p=u_1\lor\cdots\lor p=u_N).
\tag{4}
$$

Repeated witnesses are allowed. This bounds proposition objects, not current truth values, the number of observers, or an internally variable finite cardinality.

## 2. A finite permutation tuple detecting every reduced word

Write Sym(m) for the ordinary finite symmetric group on m vertices. It is used in the metalanguage, not as a new object-language type. To say Sym(m) satisfies w means that every permutation tuple substituted for the variables makes w the identity permutation.

**Lemma 1.** A nonempty reduced word of length L fails in Sym(L+1).

**Proof.** Use vertices 0,1,…,L. For each generator x_i prescribe a partial map π_i along the word path. At step j impose

$$
\begin{cases}
\pi_{i_j}(j-1)=j,&\varepsilon_j=1,\\
\pi_{i_j}(j)=j-1,&\varepsilon_j=-1.
\end{cases}
\tag{5}
$$

These prescriptions form a partial injection for each generator. Positive occurrences have distinct sources and targets among themselves, as do negative occurrences. A source collision between opposite signs could only identify the source j−1 of a positive step j with the source k of a negative step k. Then k=j−1, so the adjacent letters are x_i⁻¹ followed in application order by x_i. Reducedness excludes this. A target collision could only identify the target j of a positive step j with the target k−1 of a negative step k. Then k=j+1, giving adjacent x_i followed by x_i⁻¹, also excluded. These exhaust the possible collisions, because path edges with no common endpoint use different vertices.

For each i, the unused source and target sets have the same finite size. Match their elements in increasing order to complete π_i to a permutation of 0,…,L. If a generator has no prescribed edges, this rule gives identity. This is an explicit finite completion, not a choice principle or an assumed extension of an admitted logical operation.

At a positive step, (5) sends j−1 to j. At a negative step, π_i(j)=j−1 means π_i⁻¹ sends j−1 to j. Induction along the application order therefore gives

$$
w(\pi_1,\ldots,\pi_r)(0)=L\ne0.
\tag{6}
$$

Thus the evaluated word is nonidentity. ∎

Sym(j) embeds in Sym(j+1) by fixing the last vertex. A word identity holding in a group holds in every subgroup. Therefore the values of j≥1 for which Sym(j) satisfies w form an initial segment. Sym(1) satisfies every group word, while Lemma 1 excludes Sym(L+1). Hence the external integer

$$
\boxed{
k(w):=\max\{j\ge1:\mathrm{Sym}(j)\text{ satisfies }w\}
\quad\text{exists and satisfies }1\le k(w)\le L.}
\tag{7}
$$

In particular Sym(k(w)+1) fails w. This threshold is effectively a finite calculation: test permutation tuples in the groups of degrees at most L+1. No general theorem about free groups is required for its existence or bound.

## 3. Faithful finite permutation actions by admitted logical observers

Assume full Rev, hence C5. Fix an external m≥1 and pairwise disjoint nonzero propositions b₁,…,b_m. The [finite common-refinement lemma](bounded-exponent-reversible-observers.md), §2, supplies a nonzero proposition d and admitted reversible $\mathrm{Good}_{\{t\}}$ observers G_i, with qualified inverses H_i, such that

$$
c_i:=G_i d\ne0,\qquad c_i\le b_i.
\tag{8}
$$

That lemma uses the admitted orbit join O(d)=Top under Rev. For any nonzero target b, some qualified G has Gd∧b≠0: if every such intersection were zero, meeting b into the admitted orbit join would give zero. Shrinking d to d∧G⁻¹b then preserves every earlier nonzero image by injectivity. Repeating this for the fixed finite list proves (8). Neither nonzero d nor its intersections are assumed currently true, and no infinite family of choices is made.

Let r=¬∨ᵢc_i. For each external permutation π∈Sym(m) define the admitted term

$$
T_\pi(p):=(r\land p)\lor
\bigvee_{i=1}^{m}
\left[c_{\pi(i)}\land(G_{\pi(i)}\circ H_i)(p)\right].
\tag{9}
$$

Every composite G_{π(i)}∘H_i is Good at every requested finite list. The output regions r,c₁,…,c_m form a Boolean partition. Finite Boolean patching proves the Boolean laws for T_π. For each requested quantifier type, fixed-region distribution and the branch qualifications give existential preservation; negation and quantifier duality give universal preservation. C5 Functionality collects the full composite identities. This is the same qualified partition calculation used in the cycle theorem of the [exponent note](bounded-exponent-reversible-observers.md), §3.

The whole multiplication law requires more than checking the finite set of selected c_i. Put K_{π,i}=G_{π(i)}∘H_i. Since K_{π,i}(c_i)=c_{π(i)}, its output mask in (9) reads exactly the input region c_i. Consequently for every proposition p,

$$
T_\pi(p\land c_i)=K_{\pi,i}(p\land c_i),
\qquad
T_\pi(p\land r)=p\land r.
\tag{10}
$$

All other branches vanish in the first equation, because their input regions are disjoint from c_i. Applying T_π after T_σ to the c_i part of p gives

$$
\begin{aligned}
T_\pi(T_\sigma(p\land c_i))
&=(G_{\pi(\sigma(i))}\circ H_{\sigma(i)})
  (G_{\sigma(i)}\circ H_i)(p\land c_i)\\
&=(G_{\pi(\sigma(i))}\circ H_i)(p\land c_i).
\end{aligned}
\tag{11}
$$

The r part remains fixed. Distributing p across the finite partition and using Functionality yields exact whole-operation identities

$$
\boxed{
T_\pi\circ T_\sigma=T_{\pi\circ\sigma},
\qquad T_{\mathrm{id}}=I,
\qquad T_\pi^{-1}=T_{\pi^{-1}}.}
\tag{12}
$$

The inverse notation in the last equation refers to the explicitly admitted operation on its right, with both inverse equations following from the first two identities. Thus every T_π is an admitted qualified reversible observer.

This representation is faithful. If π≠σ, choose an index i with π(i)≠σ(i). The values

$$
T_\pi(c_i)=c_{\pi(i)},\qquad
T_\sigma(c_i)=c_{\sigma(i)}
\tag{13}
$$

are distinct, because the c_j are disjoint and nonzero. Hence T_π≠T_σ.

Equations (9)–(13) give a finite family of admitted terms with the exact group equations. They do not postulate an object-language set of permutations or an admitted map from an unprovided finite group type. For a fixed finite permutation tuple, the corresponding finite tuple of observer terms and their inverse terms is sufficient to instantiate (3).

## 4. Exact classification of each nontrivial word law

For a fixed k≥1, the elementary Boolean bound is

$$
\text{no }k+1\text{ disjoint nonzero propositions}
\quad\longleftrightarrow\quad
\mathrm{AtMost}_{2^k}(t).
\tag{14}
$$

Here is the finite reasoning. Starting with the partition {Top}, split a nonatom into two nonzero parts whenever possible. The absence of k+1 disjoint nonzeros forces termination after at most k−1 splits, with a partition into j≤k atoms. Every proposition is a finite join of these atoms, giving at most 2^k values. Conversely k+1 disjoint nonzeros give 2^{k+1} distinct finite joins, contradicting an enumeration of at most 2^k values by finite pigeonhole. These are fixed finite arguments, not an enumeration of an arbitrary internally finite domain; see also the [exponent note](bounded-exponent-reversible-observers.md), §4.

**Theorem.** For every fixed nonempty reduced word w, with k=k(w),

$$
\boxed{
\mathrm H+\mathrm{Rev}+\mathrm{Law}_w
\quad\equiv\quad
\mathrm{C5}+\mathrm{AtMost}_{2^k}(t)
\quad\equiv\quad
\mathrm H+\mathrm{End}+\mathrm{AtMost}_{2^k}(t).}
\tag{15}
$$

**Forward.** Rev supplies C5. If k+1 disjoint nonzero propositions existed, §3 would give a faithful admitted representation T of Sym(k+1). By definition of k there is a finite permutation tuple π₁,…,π_r for which w(π₁,…,π_r) is nonidentity. Use T_{π_i},T_{π_i⁻¹} as the qualified inverse pairs in (3). Repeated use of (12) gives

$$
W_w(T_{\pi_1},T_{\pi_1^{-1}},\ldots,
    T_{\pi_r},T_{\pi_r^{-1}})
=T_{w(\pi_1,\ldots,\pi_r)}\ne I,
\tag{16}
$$

where nonidentity follows from faithfulness. This contradicts Law_w. Equation (14) therefore gives AtMost_{2^k}(t).

**Converse.** C5+AtMost_{2^k}(t), together with (14), supplies a partition into j≤k atoms. Thus Atomicity_t holds, and the established C5+Atomicity_t theorem supplies full End and full Rev.

Every admitted qualified reversible observer permutes these j atoms. Since Sym(j) satisfies w, the operation W_w for any tuple of qualified inverse pairs fixes every atom. It consequently fixes every finite join of atoms and hence every proposition. Functionality gives W_w=I as a whole-operation identity, proving Law_w. No external permutation needs to be admitted in this converse; the admitted automorphisms merely induce permutations belonging to a finite group whose law is already known.

The theorem involves the full Rev or End schema and the C5 theory, not a new finite axiomatization of those backgrounds over H. Law_w and AtMost_{2^k}(t) themselves are finite sentences. All witnesses constructed in the forward proof retain the same requested finite qualification, through the C5 type-reduction theorem.

## 5. Commutativity, a metabelian law and exponent laws

Use the conventional commutator [x,y]=xyx⁻¹y⁻¹, with functional composition as in §1.

**Commutativity.** For w=[x,y], Sym(2) is abelian, while the transpositions (12),(23) do not commute in Sym(3). Hence k(w)=2, and

$$
\mathrm{Rev}+\mathrm{Law}_{[x,y]}
\quad\equiv\quad
\mathrm{C5}+\mathrm{AtMost}_{4}(t)
\tag{17}
$$

over H. This recovers the [group-centre characterization](centre-of-reversible-logical-observers.md), §4: over full Rev, commutativity of the entire qualified reversible group has the same strength as separation by its centre. A chosen commuting separating subgroup is a different condition.

**The metabelian word.** Take

$$
w=[[x_1,x_2],[x_3,x_4]].
\tag{18}
$$

This is a nonempty reduced word. In Sym(3), every commutator is an even permutation, and the even subgroup consists of identity and the two 3-cycles. That subgroup is cyclic, so any two commutators commute and (18) holds.

It fails in Sym(4). With the stated convention,

$$
[(12),(23)]=(132),\qquad
[(12),(24)]=(142).
\tag{19}
$$

The two cycles do not commute: their products in the two orders send 1 respectively to 4 and 3. Substituting (12),(23),(12),(24) in (18) therefore makes the outer commutator nonidentity. Consequently k(w)=3 and

$$
\mathrm{Rev}+\mathrm{Law}_{[[x_1,x_2],[x_3,x_4]]}
\quad\equiv\quad
\mathrm{C5}+\mathrm{AtMost}_{8}(t).
\tag{20}
$$

The terminology “metabelian” is justified directly: requiring all commutator values to commute makes the subgroup they generate abelian, and conversely an abelian commutator subgroup makes (18) hold. No assertion about further derived-length words is needed here.

**Exponent laws.** The word xⁿ for fixed external n≥1 recovers the [bounded-exponent theorem](bounded-exponent-reversible-observers.md). Sym(j) satisfies xⁿ exactly when every cycle length 1,…,j divides n: necessity uses an m-cycle, and sufficiency decomposes each permutation into disjoint cycles. Thus k(xⁿ) is precisely the previously defined k(n), and (15) specializes to that theorem without changing its scope or proof status.

For any two nontrivial words with k(w)<k(v), the w-theory together with Rev implies the v-theory strictly. A full S5 cluster with k(w)+1 worlds satisfies C5 and End, meets the larger proposition bound, and fails the smaller one. Words with equal thresholds give the same theory when added to full Rev, even when their identities are different as abstract group laws.

## 6. The nontriviality boundary

The hypothesis that the reduced word is nonempty is essential. If a word freely reduces to the empty word, the whole inverse equations in (2) already make its evaluation identity in H by successive adjacent cancellations. Its law adds nothing to Rev. Infinite full S5 models have Rev and an infinite proposition domain, so no finite bound follows in that case.

For a nonempty reduced word, (7) gives the uniform explicit upper estimate

$$
\mathrm{Rev}+\mathrm{Law}_w
\quad\vdash\quad
\mathrm{AtMost}_{2^L}(t).
\tag{21}
$$

The sharp bound is 2^{k(w)}, not necessarily 2^L. A finite word identity imposed on the whole reversible group therefore forces a genuinely fixed finite bound, stronger than merely asserting internal Frege finiteness. Conversely the theorem is not about requiring only the separating witnesses to obey a law: for example involutive separating witnesses already suffice for unrestricted Rev, without any finite proposition bound.

The construction establishes (15) by admitted terms, finite quantified arguments and the already available C5 order/Functionality laws. It uses no Boolean Completeness, Zorn, Actuality or Choice premise, no external-function admission, and no theorem identifying all external automorphisms with admitted observers.

The companion [Group identities within invariant components](invariant-components-and-group-identities.md), §§2–4, proves an exact extension over C5 without Rev: Law_w holds iff no k(w)+1 disjoint propositions have reversible orbit joins with nonzero common meet. Under Rev every nonzero orbit join is Top, so that component condition becomes the global finite bound in (15). Without Rev, the extension does not assert a finite proposition domain.

## 7. Sources

The reduced-path permutation construction, its use in the threshold k(w), the faithful whole-operation Sym(m) patch, the exact general-word classification and the explicit commutative/metabelian comparisons are original ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The admitted orbit and common-refinement ingredients are [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §§1–3, and [Bounded-exponent reversible observers](bounded-exponent-reversible-observers.md), §§2–4. The latter supplies the numerical special case, not a premise about external automorphism admission. The comparison with group-central separation is [Centre of reversible observers](centre-of-reversible-logical-observers.md), §§2–5.

The full observer results Rev⇒C5 and C5+Atomicity_t⇒End⇒Rev are [Logical observer hierarchy](../logical-observer-hierarchy.md), §§3–4. The same-observer finite-list upgrade is [Modal selectors and quantifier reduction](../modal-selectors-and-quantifier-reduction.md), §4. Whole Boolean partition patching is also proved in [Finite relative image generation](finite-relative-image-generation.md), §4.

The C framework and relational language are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.1, 1.3 and 1.5, summarized in the [background](../../source/topics/classicism/background.md). C5's [Barcan consequences](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml) and [Functionality consequence of Barcan](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml) supply the indicated quantifier and whole-identity background. The finite and infinite full S5 examples are standard full action models from *Classicism*, §3.5 and Appendix D, as recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). These sources provide the framework and earlier ingredients, not attribution for the new group-word theorem.
