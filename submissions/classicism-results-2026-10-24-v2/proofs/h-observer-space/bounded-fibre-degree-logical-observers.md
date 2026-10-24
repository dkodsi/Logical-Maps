# Bounded fibre degree and reversible logical observation

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–6, unpaginated.  The additional Boolean Completeness and Zorn premises used in §5 are identified there.

A logical observer has bounded fibre degree when only boundedly many disjoint propositions can have overlapping image ceilings. Over C5, every observer with a fixed finite degree bound has full local-transversal support. Its entire current truth profile therefore has a qualified involutive representative. Separation by these observers is exactly reversible separation, without injectivity, Boolean Completeness or Choice assumptions.

The degree bounds multiply under composition and add under Boolean patching. With Boolean Completeness and Zorn at t added, degree at most n is equivalent to a partition into n local transversals. This also gives an exact comparison with the earlier finite relative-generation condition.

## 1. An intrinsic finite degree condition

Work over C5. Fix a finite external qualification list Δ containing t, and an admitted $\mathrm{Good}_\Delta$ observer E. Good retains whole Boolean and listed quantifier composite identities. E need not be injective or onto.

Write $L_E$⊣E⊣$R_E$ for the [canonical admitted adjoints](canonical-adjoints-and-image-factorization.md), and $C_E$=E∘$L_E$ for the image closure. We use
$$
q\le C_Eq,\qquad
L_E(q\land Ep)=L_Eq\land p,\qquad
L_EEL_E=L_E.
\tag{1}
$$
The last identity is the usual triangular identity of the adjunction. In particular $L_E$ reflects zero: if $L_E$q=0, then q≤E0=0. $L_E$ preserves admitted joins and hence finite joins. It is not assumed globally Boolean or qualified as an observer.

For a fixed external integer n≥1, define degree at most n by the single finitary formula
$$
\mathrm{Deg}_n(E):=
\forall b_0\cdots b_n\left[
\bigwedge_{i<j}(b_i\land b_j=0)
\ \to\
\bigwedge_{i=0}^{n}L_Eb_i=0
\right].
\tag{2}
$$
Thus n+1 disjoint pieces cannot have a common nonzero overlap of their $L_E$-images. Equivalently, there are no n+1 disjoint pieces with one and the same nonzero $L_E$-image. Indeed, if
$$
d:=\bigwedge_i L_Eb_i\ne0,
\qquad c_i:=b_i\land Ed,
\tag{3}
$$
then Frobenius gives $L_E c_i$=d for every i. These $c_i$ remain disjoint and are all nonzero. The reverse implication is immediate.

One may equally use $C_E$ in place of $L_E$ in (2). Put a=$L_E$1. Frobenius gives $L_E$Ep=a∧p, so E reflects zero on [0,a]; all $L_E b_i$ lie in that interval. Since E preserves finite meets,
$$
\bigwedge_iL_Eb_i=0
\quad\longleftrightarrow\quad
\bigwedge_iC_Eb_i=0.
\tag{4}
$$
This describes degree directly through the least image values covering the pieces. It does not presuppose atoms, possible-world points, an external representation or the existence of set-theoretic fibres.

The condition is monotone in its bound: $\mathrm{Deg}_n$ implies $\mathrm{Deg}_{n+1}$. Every expression in (2) is an admitted term or a fixed finite tuple of proposition variables. No internal Frege finiteness, object-language quantification over n, or infinite disjunction of these formulas is intended.

## 2. Bounded degree forces full local support

Recall the admitted local-transversal predicate and support from [Local-transversal support](local-transversal-support.md):
$$
\begin{aligned}
\mathrm{Loc}_E(b)
&\quad\longleftrightarrow\quad
\forall q\,[b\land C_E(b\land q)=b\land q],\\
s_E&:=\exists b\,[\mathrm{Loc}_E(b)\land b].
\end{aligned}
\tag{5}
$$
Under C5 the locality guard can be expressed as an identity of complete unary operations and is endpoint-valued. The support is consequently the admitted join of the local transversals. Locality is hereditary, and every local b is below $s_E$.

**Splitting lemma.** If b is not local, there are disjoint x,y≤b with the same nonzero $L_E$-image.

Choose q≤b such that b∧$C_E$q≠q. The unit q≤$C_E$q gives
$$
y:=b\land C_Eq\land\neg q\ne0.
\tag{6}
$$
Put d=$L_E$y. Zero-reflection makes d nonzero. Since y≤E($L_E$q), monotonicity and (1) give
$$
d\le L_EEL_Eq=L_Eq.
\tag{7}
$$
Now set x=q∧Ed. Frobenius gives $L_E$x=$L_E$q∧d=d=$L_E$y. Also x≤q and y≤¬q, so x,y are disjoint, nonzero and below b. This proves the lemma without injectivity of E.

**Theorem 1.** For every fixed external n≥1,
$$
\boxed{\mathrm{Deg}_n(E)\ \longrightarrow\ s_E=1.}
\tag{8}
$$
Suppose instead that r=¬$s_E$ is nonzero. Begin with the one-piece tuple r. Its $L_E$-image is nonzero. Every nonzero subpiece of r fails locality, since a local subpiece would be below both $s_E$ and its complement.

Assume m disjoint pieces b₁,…,$b_m$≤r have a common nonzero $L_E$-image p. Apply the splitting lemma to b₁, obtaining x,y with common nonzero image d≤p. Replace each of the other pieces by $b_i$∧Ed. Their images are p∧d=d by Frobenius. Together with x,y they give m+1 disjoint pieces below r with the same nonzero image d. Iterating this construction a fixed n times produces n+1 pieces, contradicting $\mathrm{Deg}_n(E)$.

Only a fixed finite sequence of existential witnesses and explicit restrictions is used. There is no infinite recursion, choice function, Boolean Completeness or Zorn premise. ∎

At the smallest degree the condition is especially concrete:
$$
\boxed{\mathrm{Deg}_1(E)\ \longleftrightarrow\ E\text{ is onto}.}
\tag{9}
$$
If Deg₁ holds, the splitting lemma makes 1 local. Hence $C_E$q=q for every q, and q=E($L_E$q) supplies an admitted preimage. Conversely, if E is onto, $C_E$=I, so 1 is local. The restriction of $L_E$ to [0,1] is then a relative Boolean isomorphism onto [0,$L_E$1], by the local-interval theorem. It preserves disjointness, which is Deg₁. Equivalently, one can apply E to $L_E$b∧$L_E$c and use $L_E C_E$=$L_E$ to obtain zero when b∧c=0.

Full support is weaker than any particular finite degree bound for an individual observer. For example, the endpoint observer on the full powerset algebra of an infinite set that evaluates at a fixed atom has full support, because every singleton is local; arbitrarily many disjoint singletons have the same nonzero image ceiling. This is the same full-function example already checked in the support note, §6. The comparison below concerns separating classes, not an equivalence between individual qualifications.

## 3. Entire truth profiles and separation

The [local-transversal normalization theorem](finite-relative-image-generation.md), §4, applies to arbitrary Good E: if some local b is currently true, there is an admitted $\mathrm{Good}_\Delta$ involution T such that
$$
T\circ T=I,
\qquad \forall p\,(Tp\leftrightarrow Ep).
\tag{10}
$$
The inverse equation is a whole-operation identity. The second assertion is agreement of the entire current truth profile; it is not equality of T and E, nor necessarily persistent profile agreement.

By Theorem 1, a degree-bounded E has $s_E=1$. The existential truth clause in (5) therefore supplies a currently true local b, so (10) follows. This is a single-observer normalization theorem, not merely a consequence after assuming a separation principle.

Let $S_{\tau,\Delta}$[$\mathrm{Deg}_n$] be the full typed separation instance whose witnesses are $\mathrm{Good}_\Delta$ observers satisfying (2). Keeping τ and the finite Δ fixed, and retaining t∈Δ, (10) preserves the observed truth value at every argument tuple. Conversely a qualified reversible observer is onto and therefore satisfies Deg₁ and every $\mathrm{Deg}_n$. Hence
$$
\boxed{
S_{\tau,\Delta}[\mathrm{Deg}_n]
\ \longleftrightarrow\
S_{\tau,\Delta}[\mathrm{Rev}]
\qquad\text{over C5, for every fixed external }n\ge1.}
\tag{11}
$$
The same comparison holds for the full external schemas. It remains true if injectivity is added to the witnesses on the left, since the normalized involution is injective. No common infinite list of type qualifications or bound-free finiteness formula is being asserted. At n=1, (11) recovers the surjective/reversible separation equivalence over C5.

## 4. Composition, iteration and Boolean patching

These degree calculations require C5 only; no selection principle is used.

**Composition theorem.** If $\mathrm{Deg}_m(E)$ and $\mathrm{Deg}_n(F)$, then
$$
\boxed{\mathrm{Deg}_{mn}(F\circ E).}
\tag{12}
$$
The left adjoint of F∘E is $L_E$∘$L_F$. Let $b_i$, for i in a fixed set I of mn+1 indices, be pairwise disjoint, and put $d_i$=$L_F b_i$. The degree bound for F says that any intersection of n+1 distinct $d_i$ is zero.

Form the finite Boolean cells
$$
e_J:=\bigwedge_{i\in J}d_i\land
       \bigwedge_{i\in I\setminus J}\neg d_i
\qquad(J\subseteq I).
\tag{13}
$$
They are pairwise disjoint. A cell with |J|>n is zero, and
$$
d_i=\bigvee_{J\ni i,\ |J|\le n}e_J.
\tag{14}
$$
If ∧_{i∈I}$L_E d_i$ were nonzero, finite-join preservation and finite distributivity applied to (14) would yield a choice of $J_i$ containing i, for each of these finitely many i, with
$$
\bigwedge_{i\in I}L_Ee_{J_i}\ne0.
\tag{15}
$$
At least m+1 distinct cells occur: at most m sets of cardinality at most n cannot contain all mn+1 indices. Those distinct cells are disjoint and their $L_E$-images have nonzero common overlap, contradicting $\mathrm{Deg}_m(E)$. This proves (12). All choices in this argument are finite distributive expansions of fixed tuples, not an application of Choice.

Consequently, for fixed external k≥1,
$$
\mathrm{Deg}_n(E)\ \longrightarrow\
\mathrm{Deg}_{n^k}(E^k).
\tag{16}
$$
**Patching theorem.** For any proposition a, put
$$
G(p):=(a\land Ep)\lor(\neg a\land Fp).
\tag{17}
$$
Boolean partition patching gives all whole $\mathrm{Good}_\Delta$ identities. If $\mathrm{Deg}_m(E)$ and $\mathrm{Deg}_n(F)$, then
$$
\boxed{\mathrm{Deg}_{m+n}(G).}
\tag{18}
$$
Its left adjoint is
$$
L_Gq=L_E(a\land q)\lor L_F(\neg a\land q).
\tag{19}
$$
For m+n+1 disjoint inputs, expand the intersection of the right sides of (19). Every term selects the E-branch on more than m inputs or the F-branch on more than n inputs. The corresponding degree bound makes that term zero. Thus their finite join is zero. Repeated finite patching similarly gives the sum of the branch bounds. In particular, a patch of k onto observers over a fixed k-part Boolean partition has degree at most k, and hence has an involutive representative of its entire current truth profile.

Equations (12), (16) and (18) are upper bounds. They do not identify a least degree, assert that degrees always exist, or convert a union over all external finite bounds into one formula of the language.

## 5. With Boolean Completeness and Zorn, degree counts local sheets

For this section add the two explicit unboxed assumptions
$$
\mathrm{BC}_t+\mathrm{Zorn}_t.
\tag{20}
$$
These are [Boolean Completeness at t](../../source/topics/classicism/principles/boolean-completeness-t.yaml) and the σ=t instance of the [preorder Zorn principle](../../source/topics/classicism/principles/zorn-r.yaml). The precise current-family interpretation and the necessary chain-bound proof are given in [Zorn selects local transversals](zorn-local-transversal-selection.md), §§1–3. In particular that theorem, for arbitrary Good E, supplies
$$
\forall r\ \exists u\,
[\mathrm{Loc}_E(u)\land u\le r
 \land L_Eu=L_E(s_E\land r)].
\tag{21}
$$
$\mathrm{BC}_t$ and $\mathrm{Zorn}_t$ enter only through (21). They are not inferred from C5, and an arbitrary current predicate is not silently replaced by an endpoint-valued guard.

Say that E has n local sheets when there is a fixed tuple u₁,…,$u_n$ with
$$
\bigvee_{i=1}^n u_i=1,\qquad
u_i\land u_j=0\ (i\ne j),\qquad
\mathrm{Loc}_E(u_i)\text{ for every }i.
\tag{22}
$$
Zero sheets are allowed, so this means at most n nonzero sheets. These are admitted proposition objects, not a new indexed type.

**Theorem 2.** Under C5+$\mathrm{BC}_t$+$\mathrm{Zorn}_t$,
$$
\boxed{\mathrm{Deg}_n(E)
\quad\longleftrightarrow\quad
E\text{ has }n\text{ local sheets}.}
\tag{23}
$$
For the forward direction, Theorem 1 gives $s_E=1$. Begin with r₀=1. Use (21) a fixed n times to choose
$$
u_i\le r_{i-1},\qquad
\mathrm{Loc}_E(u_i),\qquad
L_Eu_i=L_Er_{i-1},\qquad
r_i=r_{i-1}\land\neg u_i.
\tag{24}
$$
The $u_i$ are disjoint. If $r_n$≠0, let d=$L_E r_n$≠0. Since $r_n$≤$r_{i-1}$, each $u_i$∧Ed has $L_E$-image d. These n pieces, together with $r_n$, are n+1 disjoint pieces with the same nonzero image, contrary to $\mathrm{Deg}_n(E)$. Hence $r_n$=0, proving (22).

The converse does not use (20). Let b₀,…,$b_n$ be disjoint. Because the sheets partition 1,
$$
L_Eb_j=\bigvee_{i=1}^n L_E(u_i\land b_j).
\tag{25}
$$
If the intersection of these n+1 images were nonzero, finite distributivity would choose one sheet $i_j$ for each j with a nonzero common intersection of the selected terms. Two indices j≠k would select the same sheet i. But the relative Boolean isomorphism $L_E$ on [0,$u_i$] sends the disjoint pieces $u_i$∧$b_j$ and $u_i$∧$b_k$ to disjoint images. This is a contradiction. Thus (2) holds. ∎

The theorem concerns a finite partition obtained by a fixed number of applications of (21). It uses no uniform selection function in r or E. It also does not say that the union of arbitrary local pieces is local: different sheets generally fail that compatibility condition.

## 6. Exact comparison with finite relative generation

For a fixed external k≥0, $\mathrm{FG}_k(E)$ says that the image of E and k admitted Boolean generators generate the ambient proposition algebra. Its exact finite-tuple formula is [Finite relative image generation](finite-relative-image-generation.md), §1. The resulting 2^k Boolean cells are local by that note's §2 and partition 1. The converse direction of Theorem 2 therefore gives, over C5 alone,
$$
\boxed{\mathrm{FG}_k(E)\ \longrightarrow\
\mathrm{Deg}_{2^k}(E).}
\tag{26}
$$
Conversely suppose $\mathrm{Deg}_{2^k}(E)$ and add (20). Theorem 2 gives a partition into 2^k local sheets $u_s$ indexed by the fixed bit strings s∈{0,1}^k, padding with zero sheets if necessary. Define k admitted generators
$$
a_j:=\bigvee_{s:\,s_j=1}u_s\qquad(1\le j\le k).
\tag{27}
$$
The Boolean cell determined by the generators and the string s is exactly $u_s$. Locality gives the explicit expansion
$$
q=\bigvee_s\left[u_s\land E\bigl(L_E(u_s\land q)\bigr)\right].
\tag{28}
$$
Thus $\mathrm{FG}_k(E)$ holds, with no selected family of inverse values: (28) supplies them as admitted terms. We obtain the precise equivalence
$$
\boxed{
\mathrm{C5}+\mathrm{BC}_t+\mathrm{Zorn}_t
\ \vdash\
\mathrm{FG}_k(E)\leftrightarrow
\mathrm{Deg}_{2^k}(E)
\quad\text{for every fixed external }k\ge0.}
\tag{29}
$$
For k=0 this is onto⇔degree at most 1, already valid over C5. More generally, a degree bound n supplies $\mathrm{FG}_{\lceil\log_2n\rceil}$ under (20), since one can pad an n-sheet partition to the next power of two. This is an upper bound from a given n, not a claim that the least number of generators equals ⌈log₂n⌉ when n is merely a nonminimal degree bound. Equation (29), rather than an unspecified minimality claim, is the exact fixed-bound statement.

The additional principles are needed here only for constructing a global finite sheet partition from bounded degree. The entire truth-profile normalization, reversible separation equivalence and degree calculus in §§2–4 remain C5-only results.

## Sources

- Direct source for the proofs in §§1–6: `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, this note, unpaginated.
- [Canonical adjoints and image factorization](canonical-adjoints-and-image-factorization.md), §§2–4: admitted adjoints, image closure, triangular and Frobenius identities.
- [Local-transversal support](local-transversal-support.md), §§1–5: locality, its support, interval isomorphisms and current-profile normalization.
- [Finite relative image generation](finite-relative-image-generation.md), §§1–4: the fixed $\mathrm{FG}_k$ formula, local cells, and the whole-qualified involution preserving an observer's entire current profile.
- [Zorn selects local transversals](zorn-local-transversal-selection.md), §§1–3: the explicit $\mathrm{BC}_t$+$\mathrm{Zorn}_t$ premises and controlled local selection (21).
