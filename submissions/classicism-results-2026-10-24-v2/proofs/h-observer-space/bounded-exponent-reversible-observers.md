# A uniform exponent for all reversible observers bounds the proposition algebra

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: misc, this note, §§1–5, unpaginated.

Over reversible logical separation, a fixed exponent law for every reversible observer is exactly a finite bound on the proposition algebra. The proof establishes a reusable refinement theorem: any finite disjoint family of nonzero propositions contains nonzero pieces related by admitted logical automorphisms. A finite Boolean patch then cycles these pieces and has exactly the prescribed finite order.

The restriction concerns the entire admitted reversible group. Requiring only the chosen separating witnesses to be involutions would add nothing to Rev, by the established involutive-normalization theorem. All numerical parameters below are fixed external integers; no arithmetic predicate or quantifier over iteration bounds is added to the object language.

## 1. The finite exponent sentence

Work first over C5. Write 0,1 for Bottom, Top and I=λp.p. Let A(G) be the finite predicate saying that G is $\mathrm{Good}_{\{t\}}$ and has an admitted same-qualified whole inverse:

$$
A(G):=B(G)\land\exists H^{tt}
[B(H)\land G\circ H=I\land H\circ G=I].
\tag{1}
$$

B is the conjunction of whole Boolean and type-t quantifier identities. As in [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §1, it is equivalent to $\mathrm{Good}_{\{t\}}$ over C; the translated equality clauses are redundant here. C5 makes A(G) endpoint-valued and upgrades every qualified G and inverse to every requested finite list of quantifier types.

For a fixed external integer n≥1 define the single finite sentence

$$
\mathrm{Exp}_n:=\forall G^{tt}[A(G)\to G^n=I].
\tag{2}
$$

Gⁿ is the displayed n-fold composite; Gⁿ=I is identity of complete unary operations. The quantifier ranges over every admitted member of the qualified group, not a selected separating family. Define the external integer

$$
k(n):=\max\{j\ge1:\text{ every integer }1\le m\le j
                         \text{ divides }n\}.
\tag{3}
$$

The maximum exists: 1 divides n and n+1 does not. In particular k(n)+1 does not divide n. For fixed external N≥1 write the finite proposition-domain bound

$$
\mathrm{AtMost}_N(t):=
\exists u_1\cdots u_N\ \forall p\
(p=u_1\lor\cdots\lor p=u_N).
\tag{4}
$$

Repeated witnesses are permitted. This bounds proposition objects, not current truth values, the number of observers, or an internally variable finite cardinality.

## 2. A finite common-refinement theorem

Assume full Rev, and hence C5. The [orbit-join theorem](reversible-fixed-proposition-characterization.md), §§2–3, gives

$$
O(d):=\exists G^{tt}[A(G)\land Gd]=1
\qquad(d\ne0).
\tag{5}
$$

For any nonzero d,b there is therefore an admitted A-member G such that

$$
Gd\land b\ne0.
\tag{6}
$$

Here is the extraction, including the case in which b is currently false. Meet b into (5). The admitted quantified join becomes the join of A(G)∧Gd∧b. If every qualified intersection were zero, every joinand would be zero, since ineligible guards are Bottom under C5. The join would then be zero, contradicting b≠0. Classical quantified reasoning yields (6). No current truth of b or of the intersection is inferred.

**Finite refinement lemma.** Given any fixed finite family b₁,…,b_m of pairwise disjoint nonzero propositions, there are a nonzero d and admitted A-members G₁,…,G_m such that

$$
c_i:=G_i d\ne0,\qquad c_i\le b_i
\quad(1\le i\le m).
\tag{7}
$$

The c_i are disjoint, and their principal intervals are isomorphic by the admitted restrictions of G_j∘G_i⁻¹.

Start with d=b₁ and G₁=I. Suppose (7) holds for the first j members. Use (6) with the current d and b_{j+1} to choose G, and choose an admitted qualified inverse H. Replace d by

$$
d':=d\land H(b_{j+1}).
\tag{8}
$$

Then Gd′=Gd∧b_{j+1}≠0, so d′≠0. Each earlier G_i d′ remains nonzero by injectivity and lies below G_i d≤b_i. Keep the earlier G_i and take G_{j+1}=G. This proves the lemma by ordinary external finite induction.

Only finitely many witnesses are selected, each by existential elimination in the current proof. No Choice, atom or atomlessness assumption, Boolean Completeness or Zorn principle is used. Every map is already an admitted global logical automorphism; no external interval isomorphism is presumed to extend to one.

## 3. An admitted cycle of exactly m steps

Keep the c_i,G_i from (7), choose admitted qualified inverses H_i, and read indices cyclically modulo m. Put r=¬∨ᵢc_i and define

$$
T(p):=(r\land p)\lor
\bigvee_{i=1}^{m}
[c_{i+1}\land(G_{i+1}\circ H_i)(p)].
\tag{9}
$$

Every composite G_{i+1}∘H_i is Good at every requested finite list. The output regions r,c₁,…,c_m partition Top. Finite Boolean patching therefore makes T Good at every such list: Boolean identities are checked on the regions, while fixed-region distribution through admitted quantifier meets and joins gives the quantifier laws. C5 Functionality collects the output equations into the required whole-operation identities. These are the admitted patching laws used for interval swaps in [Finite relative image generation](finite-relative-image-generation.md), §4.

The transitions satisfy

$$
(G_{i+1}\circ H_i)(c_i)=c_{i+1}.
\tag{10}
$$

Their inverses carry c_{i+1} back to c_i. Masking an input with c_i therefore leaves only its prescribed next branch in (9); every other region contributes zero. The complement r is fixed. Expanding successive composites gives, for each fixed external s≥0,

$$
T^s(p)=(r\land p)\lor
\bigvee_{i=1}^{m}
[c_{i+s}\land(G_{i+s}\circ H_i)(p)].
\tag{11}
$$

For s=0 this is the partition of p. The successor step follows because only consecutive regions overlap, and the maps telescope using H_i∘G_i=I. At s=m every map in (11) is identity, so Tᵐp=p for every p. Functionality gives

$$
T^m=I.
\tag{12}
$$

Thus T is reversible with admitted qualified inverse T^{m−1}. Moreover Tˢc₁=c_{1+s}. For 0<s<m these are distinct nonzero disjoint propositions, so Tˢ≠I. Ordinary external division of n by m and (12) give

$$
\boxed{T^n=I\quad\longleftrightarrow\quad m\mid n.}
\tag{13}
$$

Every power identity here is a whole-operation identity. Equation (11) computes the operation on every proposition, including the complement of the pieces; the argument does not infer a whole identity merely from a permutation of finitely many selected objects.

## 4. Exact exponent classification

For each fixed k≥1, the elementary Boolean bound is: there are no k+1 disjoint nonzero propositions iff AtMost_{2^k}(t).

For the forward direction, start with the partition {1}. If a member is not an atom, split it into two disjoint nonzero parts. After at most k−1 refinements there must be a partition into j≤k atoms: otherwise one more split would give k+1 disjoint nonzeros. This is a finite classical case argument, selecting a witness at each of finitely many stages. Distributing any proposition across the atomic partition expresses it as the join of a subfamily. Listing the 2ʲ joins, with repetitions if needed, proves AtMost_{2^k}(t).

Conversely, k+1 disjoint nonzero elements yield 2^{k+1} distinct finite joins. Intersecting with a piece in the symmetric difference of two subfamilies proves distinctness. The ordinary finite pigeonhole argument contradicts an enumeration of at most 2^k objects. This is not an external enumeration of an arbitrary internally finite domain.

**Theorem.** For each fixed external n≥1, with k=k(n),

$$
\boxed{
\mathrm H+\mathrm{Rev}+\mathrm{Exp}_n
\quad\equiv\quad
\mathrm{C5}+\mathrm{AtMost}_{2^k}(t)
\quad\equiv\quad
\mathrm H+\mathrm{End}+\mathrm{AtMost}_{2^k}(t).}
\tag{14}
$$

**Forward.** Rev supplies C5. If k+1 disjoint nonzero propositions existed, §§2–3 would give an admitted A-member T of exact order k+1. Exp_n would give Tⁿ=I, contradicting k+1∤n. The Boolean bound therefore gives AtMost_{2^k}(t).

**Converse.** Under C5, AtMost_{2^k}(t) gives a partition of Top into j≤k atoms by the preceding argument. In particular Atomicity_t holds. The established C5+Atomicity_t theorem gives full End and hence full Rev.

Any A-member G is a Boolean automorphism and permutes these j atoms. Each cycle has length m with 1≤m≤j≤k, so m divides n. Thus Gⁿ fixes every atom, hence every finite join of atoms and therefore every proposition. C5 Functionality gives Gⁿ=I as a whole operation. This proves Exp_n and (14).

The finite bound and Exp_n are finite formulas. C5 and Rev retain their theory/schema scopes; (14) does not finitely axiomatize them over H. The only automorphism class quantified in Exp_n is A from (1), whose C5 type reduction supplies all requested finite qualifications.

## 5. Numerical cases and exact comparisons

The index k(n), rather than the magnitude of n, controls the theory:

| Fixed exponent n | k(n) | Equivalent proposition bound under C5 |
| --- | --- | --- |
| 1 | 1 | At most 2 proposition objects |
| 2 | 2 | At most 4 proposition objects |
| 6 | 3 | At most 8 proposition objects |
| 12 | 4 | At most 16 proposition objects |
| 60 | 6 | At most 64 proposition objects |

For n=1, (14) is Extensionality: with only the two endpoints, current coextension identifies propositions, and C gives full Extensionality. Conversely Extensionality makes every Boolean observer identity.

For n=2, the result agrees with [Separation by the centre of the reversible group](centre-of-reversible-logical-observers.md): over full Rev, requiring every reversible observer to be an involution, requiring the whole reversible group to be abelian, and separation by its centre have the same four-proposition strength. Requiring only separating witnesses to be involutions is different: involutive separation is already equivalent to unrestricted Rev.

Different exponents with the same k(n) give the same theory when added to full Rev. If k(n)<k(n′), the n-theory implies the n′-theory strictly. A full S5 cluster with k(n)+1 worlds has exactly 2^{k(n)+1} proposition objects, satisfies C5 and End, and meets the larger bound since k(n)+1≤k(n′). It fails the smaller bound, so (14) makes it a separating model.

These compare the exponent laws together with Rev. The numerical sequence n=1,2,3,… is not a strict ladder, and not every finite atom threshold is asserted to occur as k(n). No infinitary disjunction of exponent bounds is used.

## 6. Sources

The finite common-refinement lemma, whole-operation cycle construction, fixed-exponent classification and comparisons are original ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source misc, this note, §§1–5, unpaginated.

The admitted orbit join and its value under Rev are in [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §§1–3. Same-list whole Boolean patching and interval swaps are in [Finite relative image generation](finite-relative-image-generation.md), §4, and [Injective separation decomposition](injective-separation-decomposition.md), §4. The group-centre comparison is proved in [Centre of reversible observers](centre-of-reversible-logical-observers.md), §§2–4.

Rev⇒C5, End⇔C5+Atomicity_t and reversible/involutive separation equivalence are established in [Logical observer hierarchy](../logical-observer-hierarchy.md), §§3–4. The fixed C framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.1, 1.3 and 1.5, summarized in the [background](../../source/topics/classicism/background.md). C5's Barcan and Functionality consequences are recorded in [C5 implies necessary Barcan](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml) and [Barcan implies Functionality](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml).

The finite full S5 clusters are standard full action models from Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). The theorem gives their new exponent comparisons without changing database records or source certificates.
