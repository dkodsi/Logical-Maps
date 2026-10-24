# Group identities within invariant proposition components

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–5, unpaginated.

Over C5, a fixed group identity for all reversible logical observers has an exact description in the invariant proposition algebra. It bounds the number of disjoint propositions whose reversible orbit joins overlap. No separation premise is required. Under reversible separation every nonzero orbit join is Top, so this component bound reduces to the previously established finite bound on all propositions.

The converse is finite and algebraic. A finite sequence of Boolean partitions becomes stable on each of finitely many invariant regions; there the selected observers permute at most the specified number of pieces. The proof uses neither a Stone representation nor an external set of fibres, Choice, Boolean Completeness or Zorn.

## 1. Qualification, orbit joins and the component condition

Work throughout over C5 in the fixed relational language. Let B(G) denote $\mathrm{Good}_{\{t\}}$, expressed using its whole Boolean and type-t quantifier identities. Over C its original translated equality clauses are redundant, so this has exactly the established qualified members. Put I=λp.p and

$$
A(G):=B(G)\land\exists H^{tt}
 [B(H)\land GH=I\land HG=I].
\tag{1}
$$

Composition means composition of admitted unary operations. Every inverse equation is identity of the whole operation, and the inverse H is admitted. The A-members form a group. By C5's type reduction each member and its inverse has every requested finite quantifier qualification; no quantifier over types is introduced.

Use the admitted orbit operation from [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §§1–4:

$$
O(p):=\exists G^{tt}[A(G)\land Gp],
\qquad
\mathrm{Inv}(u):=\forall G[A(G)\to Gu=u].
\tag{2}
$$

C5 makes A(G) an endpoint: its Boolean combination of whole identities, including the existential inverse clause, is Top when satisfied and Bottom otherwise. Thus (2) is the join of an admitted family with endpoint membership guards. It is not a join of a presumed external collection of automorphisms.

The cited proof establishes that O(p) is the least invariant proposition above p. In particular O is monotone, O0=0, p≤O(p), and, for invariant u,

$$
O(p\land u)=O(p)\land u.
\tag{3}
$$

The invariant propositions form a Boolean subalgebra. Also O(Gp)=O(p) for every A-member G: Gp≤G(O(p))=O(p) gives one inequality, and the admitted inverse gives the other. No separation hypothesis is used in these facts.

For a fixed external integer k≥1 define the finite sentence

$$
\mathcal C_k:=\forall b_1\cdots b_{k+1}\,
 \left[
  \bigwedge_{i<j}\bigl((b_i\land b_j)=0\bigr)
  \ \to\ \left(\bigwedge_{i=1}^{k+1}O(b_i)\right)=0
 \right].
\tag{4}
$$

Zero b_i are allowed and make the conclusion automatic. The bound concerns simultaneous overlap of orbit joins, not the total number of proposition objects or current truth values. Each k gives one formula, with its conjunctions expanded finitely.

For a fixed nonempty reduced group word w, Law_w and k(w) have exactly the definitions in [Group identities for reversible observers](group-identities-reversible-observers.md), §§1–2. Law_w universally quantifies a finite tuple of admitted $\mathrm{Good}_{\{t\}}$ inverse pairs and asserts that their evaluated word is the whole identity operation. The external integer k(w) is the largest j for which Sym(j) satisfies w. The finite path argument there proves its existence, with 1≤k(w)≤length(w), and supplies a permutation tuple witnessing failure in Sym(k(w)+1).

## 2. Common equivalent pieces exist exactly when orbit joins overlap

First, for any propositions d,b,

$$
\bigl(O(d)\land O(b)\bigr)\ne0
\quad\longleftrightarrow\quad
\exists G\,[A(G)\land\bigl((Gd\land b)\ne0\bigr)].
\tag{5}
$$

For the forward direction, (3) gives
O(O(d)∧b)=O(d)∧O(b). Since O0=0, O(d)∧b is nonzero. Distribute b over the admitted join (2). If every qualified Gd∧b were zero, every joinand would be zero, including those with ineligible endpoint guards; their join would therefore be zero. Classical quantified reasoning gives the required G. Conversely, a nonzero Gd∧b lies below O(d)∧O(b), since Gd≤O(d) and b≤O(b).

This is an extraction from nonzeroness, not from current truth. In particular it remains valid when d, b and the extracted intersection are all currently false.

**Common-refinement theorem.** For any fixed finite list b₁,…,b_m, m≥1,

$$
\boxed{
\left(\bigwedge_{i=1}^{m}O(b_i)\right)\ne0
\quad\longleftrightarrow\quad
\exists d,G_1,\ldots,G_m\,
 [d\ne0\land\bigwedge_i(A(G_i)\land G_i d\le b_i)].}
\tag{6}
$$

If the b_i are pairwise disjoint, the nonzero pieces c_i=G_i d are pairwise disjoint too. Their principal intervals are related by the admitted restrictions of G_jG_i⁻¹.

**Proof.** Write v=∧ᵢO(b_i), an invariant proposition. If v≠0, set d=b₁∧v. Equation (3) gives O(d)=O(b₁)∧v=v, so d≠0. Start with G₁=I.

Suppose pieces for the first j entries have been obtained, with d≠0 and d≤v. Then 0≠O(d)≤v≤O(b_{j+1}), so (5) supplies G with Gd∧b_{j+1}≠0. Choose its admitted qualified inverse H and replace d by

$$
d':=d\land H(b_{j+1}).
\tag{7}
$$

The new image Gd′=Gd∧b_{j+1} is nonzero, hence d′≠0. Every earlier G_i d′ remains nonzero by injectivity, and remains below its earlier target b_i. Also d′≤v, retaining every remaining orbit bound. Keep the earlier G_i and take G_{j+1}=G. External finite induction proves the forward implication of (6).

Conversely, if c_i=G_i d≤b_i with d≠0, then
0≠O(d)=O(c_i)≤O(b_i) for every i. Thus their finite meet is nonzero. This proves (6). ∎

Only finitely many witnesses and inverse witnesses are selected. Each selection is existential elimination within the proof. No uniformly chosen family of inverses or an external interval isomorphism is assumed.

For disjoint targets the pieces in (6) support every finite permutation. Fix inverse witnesses H_i and put r=¬∨ᵢc_i. For each external π∈Sym(m), the admitted term

$$
T_\pi(p):=(r\land p)\lor
 \bigvee_i[c_{\pi(i)}\land(G_{\pi(i)}H_i)(p)]
\tag{8}
$$

is qualified and reversible, with the whole identities
T_πT_σ=T_{πσ}, T_id=I and inverse T_{π⁻¹}. It sends c_i to c_{π(i)} and is faithful. The region-by-region calculation in the [group-word note](group-identities-reversible-observers.md), §3, proves those identities on every proposition, including the complement r. That calculation needs only the pieces and admitted inverse pairs just supplied; its use here adds no Rev assumption.

## 3. A bounded component condition implies finite symmetric-group laws

**Finite localization lemma.** Assume C5+𝒞_k. Let G₁,…,G_r be any fixed finite tuple of A-members, with admitted qualified inverses H₁,…,H_r, and let p be any proposition. There is a finite partition of Top into invariant propositions e such that, on each nonzero e, these operations preserve a finite Boolean subalgebra of [0,e], containing e∧p, with at most k atoms.

Here a finite Boolean subalgebra means an explicitly finite collection of proposition terms used in the proof. No object-language algebra type, external infinite closure or admission of arbitrary functions is postulated.

**Proof.** For each j=0,…,k let W_j be the external finite list of all formal words of length at most j in the letters G_i,H_i, including the empty word. Let 𝔅_j be the finite Boolean algebra generated by the proposition terms

$$
\{\,g(p):g\in W_j\,\}.
\tag{9}
$$

Its partition P_j is given by the Boolean cells in those finitely many generators; zero cells may be retained. The partitions successively refine, and each operation G_i or H_i sends a generator at stage j to one at stage j+1. Words need not be reduced for this construction.

List all cells of P_k as b₁,…,b_N, with zero cells allowed. They are disjoint and their join is 1. For every subset S of the fixed finite index set {1,…,N}, define

$$
e_S:=\left(\bigwedge_{i\in S}O(b_i)\right)
      \land\left(\bigwedge_{i\notin S}\neg O(b_i)\right).
\tag{10}
$$

These are invariant propositions, and all e_S form a finite Boolean partition of Top. If e_S≠0, then

$$
1\le |S|\le k,
\qquad
(e_S\land b_i)\ne0\ \longleftrightarrow\ i\in S.
\tag{11}
$$

The empty S gives zero because 1=∨ᵢb_i≤∨ᵢO(b_i). If |S|≥k+1, (4) applied to any k+1 of its disjoint b_i makes e_S zero. For i∉S, b_i≤O(b_i) gives e_S∧b_i=0. For i∈S, the restricted meet law gives
O(e_S∧b_i)=e_S∧O(b_i)=e_S≠0, so e_S∧b_i≠0. This proves (11).

Fix a nonzero e=e_S. Localize each partition by meeting its cells with e and discarding zero cells. The final partition has exactly |S|≤k nonzero cells. Thus the k refinement steps from P₀ to P_k start with at least one cell and end with at most k. Some adjacent stages j,j+1 have the same number of nonzero cells. A finite refinement with unchanged cell count has identical cells, so their localized finite Boolean algebras coincide:

$$
e\land\mathfrak B_j=e\land\mathfrak B_{j+1}.
\tag{12}
$$

Every selected G_i and H_i fixes e. Applying one to a generator e∧g(p) at stage j therefore gives e∧(G_i g)(p) or e∧(H_i g)(p), belonging to stage j+1 and hence, by (12), to stage j. Boolean preservation makes the whole localized algebra closed under both operations. Their whole inverse identities make the restrictions mutually inverse automorphisms of that finite algebra.

In particular every longer word applied to e∧p stays in it. All later localized algebras, including stage k, consequently coincide with it. Its atoms are the nonzero cells e∧b_i for i∈S, so there are at most k. This proves the lemma. The possibly different stabilization stage for each e_S is selected from a fixed finite list, not by an infinite choice principle. ∎

**Consequence.** For each fixed k≥1, C5+𝒞_k proves every fixed word identity valid in Sym(k), as an identity of all admitted qualified reversible observers.

To see this, take any qualified inverse tuple and any p. On each nonzero e_S from the lemma, its operations permute the j≤k atoms of the localized algebra. Sym(j) is a subgroup of Sym(k), so the chosen word holds for this permutation tuple. It fixes every atom and therefore e_S∧p. Since every operation fixes e_S, the word operation W satisfies

$$
e_S\land Wp=W(e_S\land p)=e_S\land p.
\tag{13}
$$

Joining the finitely many invariant regions gives Wp=p. As p was arbitrary, C5 Functionality gives W=I as a whole unary identity. This is the required Law sentence, not merely pointwise material agreement. No optional qualification or partition hypothesis has been necessitated.

This consequence is stated one fixed word at a time. We do not need or assert its converse for arbitrary k by an appeal to abstract group-variety theory.

## 4. Exact characterization for each nontrivial word

**Theorem.** For every fixed nonempty reduced group word w, with the finite threshold k=k(w),

$$
\boxed{\mathrm{C5}\ \vdash\
 \mathrm{Law}_w\quad\longleftrightarrow\quad\mathcal C_{k(w)}.}
\tag{14}
$$

**Forward.** If 𝒞_k fails, there are k+1 pairwise disjoint propositions b_i whose orbit joins have nonzero common meet. Equation (6) supplies disjoint nonzero equivalent pieces c_i and the admitted faithful Sym(k+1) action (8). By definition of k(w), some finite tuple of permutations in Sym(k+1) makes w nonidentity. Substitute their corresponding T_π and explicitly admitted inverse T_{π⁻¹} operations into Law_w. The whole multiplication equations for (8) make the resulting word nonidentity, contradicting Law_w. Thus 𝒞_k holds.

**Reverse.** Sym(k(w)) satisfies w. The finite localization consequence of §3 therefore proves Law_w from 𝒞_k. ∎

Both sides of (14) are finite formulas for the specified external word and integer. The background remains the C5 theory. There is no full Rev premise and no claim that C5 itself has become finitely axiomatized over H. The qualifications remain whole identities throughout, with the same admitted inverse pairs supplying every requested finite list.

For example, commutativity of all qualified reversible observers is exactly 𝒞₂ over C5. The metabelian word [[x₁,x₂],[x₃,x₄]] is exactly 𝒞₃. For the exponent word xⁿ, the bound is 𝒞_{k(n)}, where k(n) is the largest j such that every integer 1,…,j divides n. These thresholds and their finite witnesses are checked in the [group-word note](group-identities-reversible-observers.md), §5, and [bounded-exponent note](bounded-exponent-reversible-observers.md), §§4–5.

## 5. Relation to separation and to the inverse frontier

Under Rev, O(b)=1 for every nonzero b. Consequently 𝒞_k then says exactly that no k+1 disjoint nonzero propositions exist. The elementary finite Boolean splitting argument makes this equivalent to AtMost_{2^k}(t), recovering the exact full-Rev classification in the group-word note.

Without Rev, equation (14) is a component bound. It does not identify the invariant propositions with the endpoints or assert a global bound on proposition objects. The proof constructs finite localized algebras only for the selected finite tuple of operations and the selected p; it does not assert that every invariant region has a finite full proposition interval.

Equation (6) also locates the homogeneity supplied by reversible motion precisely. Nonzero overlap of the invariant orbit joins suffices for equivalent nonzero subpieces, and is necessary. It does not give an isomorphism of the entire target intervals, a uniform choice of partial isomorphisms, or an inverse for an arbitrary injective logical observer. In particular, if disjoint nonzero a,b have O(a)∧O(b)=0, no such reversible common refinement can cross that invariant boundary.

The existing support theorem says that every Good observer agrees with a reversible invariant u on its local support. A detector of a false invariant must therefore act outside that support. The present finite-refinement result does not establish support coverage for that detector and does not supply the controlled inverse selection required by $\mathrm{BC}_t$+$\mathrm{Zorn}_t$. The question C5+OS+J⇒Rev∨K, equivalently the remaining injective-versus-qualified-left-inverse separation comparison, remains unresolved here.

## 6. Sources

The exact common-refinement criterion, finite invariant localization, and C5-only characterization (14) are original ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–5, unpaginated.

The admitted orbit operation, endpoint guards and invariant meet law are [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §§1–4. The complementary support interpretation is [Invariant components and local support](invariant-components-and-local-support.md), §§2–5. The finite inverse-pair syntax, explicit bound on k(w), and whole faithful permutation patch are [Group identities for reversible observers](group-identities-reversible-observers.md), §§1–3. The preceding Rev-based common-refinement and cycle arguments are [Bounded-exponent reversible observers](bounded-exponent-reversible-observers.md), §§2–4; the present criterion removes Rev by retaining the exact orbit-overlap premise.

The same-observer type reduction is [Modal selectors and quantifier reduction](../modal-selectors-and-quantifier-reduction.md), §4. The fixed C framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.1, 1.3 and 1.5, summarized in the [background](../../source/topics/classicism/background.md). C5's [Barcan consequences](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml) and [Functionality consequence](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml) supply the stated quantifier order and whole-identity background. These sources provide the framework and earlier ingredients, not attribution for the new theorem.
