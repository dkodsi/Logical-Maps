# Invariant propositions and the local support of logical observers

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§2–5, unpaginated.

Over C5, the propositions fixed by every reversible logical observer are exactly those respected on the local-transversal support of every logical observer. Equivalently, they are fixed by every canonically normalized observer. The same invariant algebra can also be described without global automorphisms: its two complementary intervals admit no nonzero relatively isomorphic parts across them.

These facts give two further formulas for the admitted reversible orbit join. They also locate precisely the obstruction when an injective observer accepts a false invariant proposition. Its change lies outside its local support. A qualified inverse with a true kernel follows under the established completeness and Zorn assumptions if that support covers the input; this coverage is not proved automatically.

## 1. Exact qualification and admitted terms

Work over C5 in the fixed relational language. Write 0,1 for Bottom, Top, and p≤q iff p∧q=p. Let B(E) be the finite conjunction of the whole Boolean and type-t quantifier identities in $\mathrm{Good}_{\{t\}}$. The redundant translated equality clauses follow over C. Define

$$
A(E):=B(E)\land\exists F^{tt}
 [B(F)\land EF=I\land FE=I],
\qquad
\mathrm{Inv}(u):=\forall E^{tt}[A(E)\to Eu=u].
\tag{1}
$$

All compositions and inverse equations in this note are identities of the complete unary operations. An inverse must be an admitted tt object. The same-observer C5 type-reduction theorem makes every B-qualified operation, and every B-qualified inverse, Good at each requested finite list. Thus (1) is one finite formula; no quantification over types or infinitary qualification is intended. See [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §1.

For a B-qualified E, use its admitted adjoints $L_E$⊣E⊣R_E and image closure $C_E$=E $L_E$. They satisfy

$$
q\le C_Eq,
\qquad L_E(q\land Ep)=L_Eq\land p.
\tag{2}
$$

$L_E$ preserves all admitted joins, but is not presumed Boolean or Good. It is the existing lambda term obtained from

$$
R_Eq:=\exists p[(Ep\le q)\land p],
\qquad L_Eq:=\neg R_E(\neg q).
\tag{3}
$$

These terms are syntactically defined for every E. Their adjunction laws are used only under B(E).

The local-transversal predicate and canonical support are

$$
\begin{aligned}
\mathrm{Loc}_E(b)&:\longleftrightarrow
 \forall q[b\land C_E(b\land q)=b\land q],\\
s_E&:=\exists b[\mathrm{Loc}_E(b)\land b],\\
\mathcal N(E)(p)&:=(s_E\land Ep)\lor(\neg s_E\land p).
\end{aligned}
\tag{4}
$$

Use equality of the complete unary operations as the definition of the Loc guard; Functionality makes this equivalent to the displayed pointwise formula. C5 makes B(E), A(E) and Loc_E(b) endpoint-valued. For A this includes the inverse existential: Boolean combinations and quantification of identity judgments retain endpoint values by C5's Barcan principles. A false guard therefore contributes 0 to each join below. This does not endpointify arbitrary currently true predicate membership.

The [support theorem](local-transversal-support.md), §§1–5, supplies heredity of locality, $s_E=1$ for reversible E, and B(N(E)) with s_{N(E)}=1 whenever B(E). It also supplies the relative isomorphism

$$
[0,L_Eb]\longrightarrow[0,b],\quad p\longmapsto b\land Ep,
\qquad q\longmapsto L_Eq
\tag{5}
$$

when b is local. Intervals are guarded ranges in the original proposition type, not new types. All definitions in this note are admitted lambda terms in their displayed parameters.

## 2. No relative isomorphism can cross an invariant boundary

An admitted relative isomorphism between [0,a] and [0,b] means admitted operations α,β whose restrictions are inverse order isomorphisms. Normalize them by masking their inputs with a,b. Their output ranges then lie below b,a, and

$$
\beta\alpha(p)=a\land p,
\qquad \alpha\beta(q)=b\land q.
\tag{6}
$$

The relative Boolean laws follow from the order isomorphism. The admitted inverse also gives every relative quantifier law: test each proposed output against arbitrary lower or upper bounds in the target interval, move the bound through the inverse, and use C5's admitted quantifier bounds. Functionality collects the full composite identities. This is precisely the interval argument in [Local homogeneity](local-homogeneity-and-split-observers.md), §1; it uses no selected family of inverse values or external completeness. The standing type domains are inhabited, as required for these relative quantifier bounds.

**Theorem 1.** For every proposition u,

$$
\boxed{\mathrm{Inv}(u)
\quad\longleftrightarrow\quad
\text{there are no nonzero }a\le u,\ b\le\neg u
\text{ with an admitted relative isomorphism}.}
\tag{7}
$$

**Proof.** Suppose such a,b,α,β exist. They are disjoint. Put r=¬(a∨b) and define

$$
T(p):=\alpha(a\land p)\lor\beta(b\land p)\lor(r\land p).
\tag{8}
$$

The three output regions are b,a,r. Their relative Boolean and quantifier laws make T Good at every requested finite list. Equation (6) gives T²=I by expanding those disjoint branches; Functionality makes this a whole-operation identity. Thus A(T). Since a≤u and b≤¬u, the b-part of Tu is α(a)=b. If u is invariant, b≤Tu=u contradicts b≤¬u and b≠0.

Conversely, suppose an admitted automorphism G moves u. If Gu∧¬u≠0, put b=Gu∧¬u and a=G^{-1}b. Then a is nonzero and below u; the restrictions of G and its admitted inverse give the required isomorphism onto b≤¬u. If instead Gu∧¬u=0, then Gu<u. Applying the inverse to the nonzero u∧¬Gu gives G^{-1}u∧¬u≠0, reducing to the first case with G^{-1}. Hence absence of a crossing isomorphism implies invariance. ∎

The theorem concerns admitted relative maps. Abstract isomorphism of two external Boolean intervals is not enough. Both directions supply or use whole logical observers at the same requested finite lists.

## 3. Local support respects exactly the reversible invariants

**Theorem 2.** Over C5, for every u,

$$
\boxed{
\begin{aligned}
\mathrm{Inv}(u)
&\longleftrightarrow
 \forall E[B(E)\to s_E\land Eu=s_E\land u]\\
&\longleftrightarrow
 \forall E[B(E)\to\mathcal N(E)u=u].
\end{aligned}}
\tag{9}
$$

**Proof.** Assume Inv(u), fix B(E), and let b be local for E. Set

$$
v:=b\land Eu\land\neg u,
\qquad a:=L_Ev.
\tag{10}
$$

Locality is hereditary, so v is local. Since v≤Eu, adjunction gives a≤u. If v≠0, then a≠0: the unit v≤E a would otherwise force v=0. Formula (5) therefore supplies a crossing relative isomorphism between [0,a] and [0,v], contrary to (7). Consequently b∧Eu∧¬u=0.

The complement ¬u is invariant as well. Apply the same argument to it and use E¬u=¬Eu. This gives b∧¬Eu∧u=0. Hence

$$
b\land Eu=b\land u
\qquad(\mathrm{Loc}_E(b)).
\tag{11}
$$

Multiply by the endpoint Loc guard and take the admitted join over b. Fixed-meet distributivity gives $s_E$∧Eu=$s_E$∧u. No observer injectivity or ordinary separation was assumed.

The second equivalence in (9) is the Boolean expansion of N(E): on ¬$s_E$ it is already identity, so N(E)u=u says exactly that its $s_E$ parts agree. For the converse to invariance, every reversible G has s_G=1 and N(G)=G. Either universal condition in (9) therefore gives Gu=u. ∎

One corresponding adjoint identity is

$$
\boxed{L_E(s_E\land u)=L_E(s_E)\land u
\qquad(\mathrm{Inv}(u),\ B(E)).}
\tag{12}
$$

Indeed replace $s_E$∧u by $s_E$∧Eu using (9), then apply Frobenius (2). This is a law for $L_E$ after restriction to $s_E$, not an assertion that $L_E$ is globally logical.

Thus the invariant Boolean algebra is exactly the common fixed algebra of the admitted class N(Good). This strengthens agreement of those classes' separation principles: it is identity of their fixed proposition objects, without a separation assumption.

## 4. The same orbit join from arbitrary normalized observers

Recall the admitted reversible orbit closure

$$
O(p):=\exists G^{tt}[A(G)\land Gp].
\tag{13}
$$

It is the least invariant proposition above p by [Reversible fixed propositions](reversible-fixed-proposition-characterization.md), §2. In particular p≤O(p), Inv(O(p)), and O is monotone and idempotent.

**Theorem 3.** The following are exact identities of admitted proposition outputs:

$$
\boxed{
O(p)
=\exists E^{tt}[B(E)\land s_E\land Ep]
=\exists E^{tt}[B(E)\land\mathcal N(E)p].}
\tag{14}
$$

For a B-qualified E, monotonicity and (9), applied to invariant O(p), give

$$
s_E\land Ep\le s_E\land E(O(p))
=s_E\land O(p)\le O(p).
\tag{15}
$$

Also N(E) is monotone and fixes O(p), so N(E)p≤O(p). The endpoint B guard removes unqualified E, and the admitted-join bound proves that both joins in (14) are at most O(p).

Conversely, every A-qualified G is B-qualified and has s_G=1 and N(G)=G. Each qualified reversible joinand in (13) is therefore a joinand in both displayed families, while an ineligible joinand is 0. Taking admitted joins gives the reverse inequalities. This proves (14). Functionality also collects (14) into equality of the complete operations in p.

Only admitted families of type (tt)t occur here. No actual extension of an arbitrary predicate is replaced by an external set, and no simultaneous family of reversible representatives is selected. In particular (14) is not obtained by choosing a same-profile involution for each E.

## 5. What an injective detector must do

Suppose u is a nonzero false invariant and B(E) with Eu currently true. Define the crossing proposition

$$
c:=Eu\land\neg u.
\tag{16}
$$

Then c is currently true, and (9) yields c∧$s_E$=0. Every local transversal lies below $s_E$, so c contains no nonzero local E-transversal. In particular $s_E$ is currently false. This conclusion holds without assuming E injective: any observer detecting the false invariant must change it entirely outside its local support.

For an exact inverse consequence, now add the explicit current premises $\mathrm{BC}_t$ and $\mathrm{Zorn}_t$ and suppose E is injective. The [controlled support-selection theorem](zorn-local-transversal-selection.md), §4, says that a qualified left inverse F killing c exists exactly when

$$
L_E(s_E\land\neg c)=1.
\tag{17}
$$

Since $s_E$≤¬c, this condition is simply $L_E s_E=1$. Thus

$$
\boxed{
\mathrm{Inj}(E)\land L_Es_E=1
\ \Longrightarrow\
\exists F[B(F)\land FE=I\land Fc=0]
\quad\text{under C5+BC}_t+\mathrm{Zorn}_t.}
\tag{18}
$$

Here E and c remain the detector and the true crossing from (16). The resulting pair witnesses $K_{\{t\}}$, and the same E,F meet every requested finite qualification. Neither $\mathrm{BC}_t$ nor $\mathrm{Zorn}_t$ is assumed necessary, and no choice of an inverse simultaneously for every E occurs.

The obstruction can also be stated on the input side. If $L_E s_E$≠1, set a=¬$L_E s_E$. Then

$$
a\ne0,\qquad Ea\le\neg s_E.
\tag{19}
$$

The second inequality follows by complementing $s_E$≤E($L_E s_E$). If E is injective, Ea≠0 and its restriction embeds the nonzero interval [0,a] into [0,Ea]. That output interval contains no nonzero local E-transversal. This is an admitted relative logical embedding, not an asserted isomorphism onto the entire output interval or a supplied inverse.

Consequently a model of C5+$\mathrm{BC}_t$+$\mathrm{Zorn}_t$+InjSep+¬Rev+¬K must have the following concrete behavior. The fixed-proposition theorem supplies a nonzero false invariant u. An injective separator of u from 0 accepts u. Every such detector has a true crossing outside its local support and must satisfy $L_E s_E$≠1; otherwise (18) gives K. Each therefore has the nonzero input interval described in (19).

This is a necessary obstruction, not a countermodel and not a solution to InjSep⇒SplitMono or OS+J⇒Rev∨K. Without the explicit $\mathrm{BC}_t$+$\mathrm{Zorn}_t$ premises, this note does not infer a qualified inverse from $L_E s_E=1$. It also does not infer that the support coverage holds merely from ordinary or injective separation.

## 6. Sources

The no-crossing characterization, common fixed algebra, orbit formulas and detector consequences are new ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–5, unpaginated.

The finite reversible guard and least invariant orbit join are [Reversible separation and fixed propositions](reversible-fixed-proposition-characterization.md), §§1–4. The admitted adjoints and Frobenius laws are [Canonical adjoints](canonical-adjoints-and-image-factorization.md), §§2–4. Locality, support and normalization are [Local-transversal support](local-transversal-support.md), §§1–5. The relative interval maps and whole involutive patch are also established in [Finite relative image generation](finite-relative-image-generation.md), §§2–4, and [Injective separation decomposition](injective-separation-decomposition.md), §4. Admission and the all-type qualification of relative order isomorphisms are detailed in [Local homogeneity](local-homogeneity-and-split-observers.md), §1. The controlled inverse criterion retaining both $\mathrm{BC}_t$ and $\mathrm{Zorn}_t$ is [Zorn local-transversal selection](zorn-local-transversal-selection.md), §§3–5.

The fixed C framework and relational language are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.1, 1.3 and 1.5, as summarized in the [background](../../source/topics/classicism/background.md). That source supplies the framework, not attribution for the new arguments. No central atlas, published proof, database record, named human review or formal-verification status is changed by this note.
