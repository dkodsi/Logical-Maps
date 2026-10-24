# Finite generation over an observer's image

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source: `misc`, this note, §§1–6, unpaginated.

Over C5, finite Boolean generation over the image of an injective logical observer gives a controlled qualified left inverse. Without assuming injectivity, finite generation still makes the observer's entire current truth profile realizable by a qualified involution. Thus separation by logical observers with this finite relative-generation condition is exactly reversible separation, for each fixed external finite bound on the number of generators.

The one-observer condition J from the injective-separation decomposition also becomes stronger under this hypothesis: a finitely generated J witness supplies the true-kernel inverse pair K. Conversely every K witness gives a J witness whose image extension needs just one Boolean generator. These statements concern generation over an observer's image, not finiteness of the proposition domain or finite output range.

## 1. Fixed finite generators and the image adjoints

Work over C5. Fix a finite external list Δ containing t and a $\mathrm{Good}_\Delta$ observer E, initially without assuming injectivity. Good uses whole Boolean and listed quantifier composite identities. Use 0,1 for Bottom, Top and p≤q for p∧q=p. The controlled inverse theorem in §3 and the J/K results in §§5–6 add injectivity explicitly; the locality and truth-profile arguments in §§2 and 4 do not.

The [canonical adjoints](canonical-adjoints-and-image-factorization.md), §§2–4, are admitted terms L,R satisfying

$$
L\dashv E\dashv R,\qquad C_E:=EL,
\tag{1}
$$

where C_E is the least image value above its input. We use its finite-join preservation, q≤C_Eq, and

$$
L(q\land Ep)=Lq\land p.
\tag{2}
$$

These adjunction and Frobenius laws hold for arbitrary Good E. L preserves every admitted existential quantifier. It is not assumed globally Boolean or Good. If E is injective, the further identities LE=I=RE hold; they are not used to obtain the local interval isomorphisms below.

Fix an external natural number n≥0. For an admitted tuple b₁,…,bₙ and each s∈{0,1}ⁿ, let

$$
b_s:=\bigwedge_{i=1}^n b_i^{s_i},
\qquad b_i^1=b_i,\quad b_i^0=\neg b_i.
\tag{3}
$$

For n=0 there is one cell, b_∅=1. The cells form a finite Boolean partition; some may be zero. Define $\mathrm{FG}_n(E)$ by

$$
\exists b_1\cdots b_n\ \forall q\ \exists(p_s)_{s\in\{0,1\}^n}
\left[q=\bigvee_s(b_s\land Ep_s)\right].
\tag{4}
$$

Both tuples in (4) are fixed finite tuples of proposition variables. This is a single formula for each external n, with no object-language quantifier over n. It says exactly that the image of E together with those n propositions generates the ambient Boolean algebra by finite Boolean operations: distributing any Boolean expression into the cells gives (4), and every right side of (4) belongs to the generated algebra.

No internal Frege finiteness, finite-range observer condition, uniform choice of the p_s, or external completeness assumption is included. The ambient proposition algebra may be infinite and atomless. FG_0(E) says E is onto. Repeating a generator, or padding with 0, shows $\mathrm{FG}_n(E)$ implies FG_{n+1}(E).

## 2. The cells are local Boolean transversals

Call v a local transversal for E when

$$
\forall q\,[v\land C_E(v\land q)=v\land q].
\tag{5}
$$

This omits the global coverage condition C_Ev=1. Every cell b_s from (4) is a local transversal. If q≤b_s, mask its finite expansion by b_s to get q=b_s∧Ep_s. Then (2) gives

$$
Lq=Lb_s\land p_s,
\qquad b_s\land E(Lq)=b_s\land E(Lb_s)\land Ep_s=q,
\tag{6}
$$

using b_s≤E(Lb_s). Applying (6) to b_s∧q proves (5).

The property is hereditary: if v≤b and b satisfies (5), then

$$
v\land C_E(v\land q)
\le v\land C_E(b\land q)=v\land q,
\tag{7}
$$

and the reverse inequality follows from x≤C_Ex. Thus every subproposition of a cell is also a local transversal.

For any such v, put a=Lv. The admitted maps

$$
p\longmapsto v\land Ep\quad(p\le a),
\qquad q\longmapsto Lq\quad(q\le v)
\tag{8}
$$

are mutually inverse Boolean isomorphisms between the two principal intervals. The first composite is (2); the other is (5). Their relative Boolean laws and admitted-join preservation are the same interval calculation as in [Injective separation decomposition](injective-separation-decomposition.md), §4. An interval here is a guarded range in the original proposition type, not a new type.

## 3. A qualified left inverse can avoid a prescribed image gap

**Theorem 1.** Assume E is injective and $\mathrm{FG}_n(E)$. For any admitted r with Lr=1, there is an admitted global Boolean transversal u≤r. Consequently there is a $\mathrm{Good}_\Delta$ observer F with F∘E=I. If Rc=0, F can be chosen so that Fc=0.

**Proof.** Fix the generators and order their finitely many cells as b₁,…,b_N, where N=2ⁿ. Set

$$
v_i:=b_i\land r,\qquad a_i:=Lv_i.
\tag{9}
$$

Each v_i is local by §2. Finite-join preservation gives ∨ᵢa_i=Lr=1. Disjointify their image coverages in the domain:

$$
d_i:=a_i\land\neg\bigvee_{j<i}a_j,
\qquad u_i:=v_i\land Ed_i,
\qquad u:=\bigvee_i u_i.
\tag{10}
$$

The d_i form a finite partition of 1. Frobenius and d_i≤a_i give

$$
Lu_i=a_i\land d_i=d_i,
\qquad C_Eu_i=Ed_i.
\tag{11}
$$

Each u_i is local, since u_i≤v_i. Their image ceilings are pairwise disjoint. Hence

$$
\begin{aligned}
u\land C_E(u\land q)
&=\bigvee_{i,j}\bigl[u_i\land C_E(u_j\land q)\bigr]\\
&=\bigvee_i(u_i\land q)=u\land q.
\end{aligned}
\tag{12}
$$

For i≠j the term is zero because u_i≤Ed_i and C_E(u_j∧q)≤Ed_j. The diagonal terms use locality. Also

$$
C_Eu=\bigvee_i Ed_i=1,
\qquad u\le r.
\tag{13}
$$

Thus u satisfies both conditions of the [Boolean-transversal theorem](injective-observers-and-boolean-transversals.md), §§2–3. Its explicit inverse

$$
F(q):=L(u\land q)
\tag{14}
$$

is $\mathrm{Good}_\Delta$ and satisfies F∘E=I as a whole identity. The same theorem verifies its Boolean laws and every listed quantifier law; no global qualification of L is assumed.

For an arbitrary left inverse take r=1. For the last assertion take r=¬c: Rc=0 gives L(¬c)=¬Rc=1. The resulting u≤¬c makes Fc=L(u∧c)=0. All constructions are finite admitted terms in the displayed parameters. ∎

## 4. Every current truth profile already has an involutive representative

**Theorem 2.** Let E be any $\mathrm{Good}_\Delta$ observer with a currently true local transversal b. Then an admitted qualified involution T satisfies

$$
\forall p\,(Tp\leftrightarrow Ep).
\tag{15}
$$

This is current material agreement of entire truth profiles, not identity T=E or necessary agreement.

**Proof.** Fix the true local transversal b. If E preserves every current truth value, use T=I.

Otherwise there is a currently false d with Ed true. If the original disagreement has the opposite orientation, use the complement of that proposition and E's negation law. Put

$$
v:=b\land Ed\land\neg d,
\qquad a:=Lv,
\qquad r:=\neg(v\lor a).
\tag{16}
$$

The proposition v is true and remains local. Adjunction gives a≤d, since v≤Ed. Thus v∧a=0, and v,a,r form a Boolean partition. Define

$$
T(p):=(v\land Ep)\lor L(v\land p)\lor(r\land p).
\tag{17}
$$

This swaps the isomorphic intervals in (8) and uses identity on the remaining region. Here are the qualification and inverse checks. The middle branch has top a and relative complement law L(v∧¬p)=a∧¬L(v∧p); the first branch has top v and the corresponding relative Boolean laws. The disjoint partition therefore gives all global Boolean laws for T. For every listed type σ,

$$
L(v\land\exists x^\sigma Hx)
=L(\exists x^\sigma(v\land Hx))
=\exists x^\sigma L(v\land Hx).
\tag{18}
$$

E's qualification handles the first branch, and fixed-guard distributivity handles the third. Their finite join commutes with ∃. Negation and duality give the universal laws, and C5 Functionality gives the full composite identities. Boolean qualification supplies the translated equality clauses.

For the square, v≤Ed and v≤¬d imply v∧Ev=0. Also v≤Ea and r≤¬a imply v∧Er=0. The local inverse identities give

$$
v\land E(Tp)=v\land p,\qquad
L(v\land Tp)=a\land p,\qquad
r\land Tp=r\land p.
\tag{19}
$$

Thus T(Tp)=p, and Functionality gives T∘T=I. Finally v is true, so the other two output regions are false and Tp has exactly the current truth value of Ep, for every p. This proves (15). ∎

In particular $\mathrm{FG}_n(E)$ supplies the premise: its finitely many cells join to 1, so at least one is currently true, and §2 makes that cell local. For a fixed n, let S_{τ,Δ}[$\mathrm{FG}_n$] require the same observer to be $\mathrm{Good}_\Delta$ and satisfy (4). Theorem 2 preserves each observed truth value at every argument tuple. Conversely a qualified reversible observer is onto, so satisfies FG_0 and hence $\mathrm{FG}_n$. Therefore

$$
\boxed{
S_{\tau,\Delta}[FG_n]
\quad\longleftrightarrow\quad
S_{\tau,\Delta}[\mathrm{Rev}]
\qquad\text{over C5, for every fixed external }n\ge0.}
\tag{20}
$$

This also holds for the full schemas with C5 retained, and remains true if injectivity is added to the separating witnesses on the left. For n=0 it recovers the earlier equivalence of surjective and reversible logical separation over C5. No bound-free finiteness formula is being defined by a disjunction over standard n. The qualification $\mathrm{FG}_n$ is the precise finitary formula (4).

More generally, separation by $\mathrm{Good}_\Delta$ observers each admitting a currently true local transversal is exactly reversible separation: Theorem 2 proves one direction, and a reversible observer has C_E=I, so 1 is a true local transversal. This too remains equivalent if injectivity is added. It is a comparison of separating classes; no converse says that an individual E whose profile has an involutive representative must itself admit a true local transversal.

## 5. The true-kernel condition has a one-generator characterization

Recall J_Δ from [Injective separation decomposition](injective-separation-decomposition.md), §1: an injective $\mathrm{Good}_\Delta$ observer E and a currently true c satisfy Rc=0. Let J_Δ^{(n)} add $\mathrm{FG}_n(E)$ to that same witness. Theorem 1 immediately gives

$$
J_\Delta^{(n)}\ \longrightarrow\ K_\Delta,
\tag{21}
$$

where K_Δ asserts a qualified pair F∘E=I and a currently true c with Fc=0. The true proposition can be kept unchanged.

Conversely suppose K_Δ. Let F,E be its pair and let k be F's greatest kernel element. It is currently true because it contains the given true kernel proposition. Set a=¬k. The [kernel and section identities](injective-observers-and-boolean-transversals.md), §3, give

$$
F k=0,\qquad Fa=1,\qquad
a\land E(Fq)=a\land q.
\tag{22}
$$

Form a new admitted Good observer

$$
E'(p):=(k\land p)\lor(a\land Ep).
\tag{23}
$$

Boolean partition patching gives whole qualification. It is injective: equality of E'p,E'q implies a∧Ep=a∧Eq; applying F gives p=q. Likewise E'p≤k implies p=0, so the same true k supplies the J condition for E'.

Its image extension is generated by the single proposition k. Indeed for every q,

$$
q=(k\land E'q)\lor(a\land E'(Fq)).
\tag{24}
$$

The first summand is k∧q, and the second is a∧E(Fq)=a∧q by (22). Thus FG_1(E'). Combining (21)–(24),

$$
\boxed{K_\Delta\quad\longleftrightarrow\quad J_\Delta^{(1)}.}
\tag{25}
$$

More generally K_Δ↔J_Δ^{(n)} for every fixed n≥1, by padding the generators. For n=0 the J condition is impossible: an injective onto E cannot have a nonzero c with Rc=0.

There is no conflict between (20) and (25). One finitely generated J witness need not separate arbitrary pairs. The E' in (23) in fact preserves current truth because k is true. Theorem 2 therefore does not turn K alone into Rev. The open C5 comparison OS+J⇒Rev∨K is not settled; this note proves its positive finite-relative-generation case and identifies precisely why a potential remaining obstruction must avoid it.

## 6. The interval interpretation

The conditions also have an exact structural reading using admitted relative logical maps. A relative map α into [0,d] has top value d, bottom 0, relative negation α(¬p)=d∧¬αp, and preserves the Boolean operations and listed quantifiers as identities. Its values lie below d. The guarded interval is not a new type; a relative inverse is an admitted ambient term whose equations are required on that interval. Whole identities are collected with the available Functionality.

Over C5, J_Δ is equivalent to an admitted relative logical embedding of the entire proposition algebra into a currently false principal interval. From E,c take d=¬c and α(p)=d∧Ep. The J condition makes α injective: αp=αq implies E(p△q)≤c and hence p=q. Its relative preservation laws follow from E and fixed-guard distributivity. Conversely, from such an α define

$$
E(p):=\alpha(p)\lor(\neg d\land p).
\tag{26}
$$

This is an injective Good observer; masking by d recovers α. If Ep≤¬d, then αp=0=α0 and p=0. Since ¬d is true, this is J_Δ.

K_Δ is the corresponding existence of an admitted relative logical **isomorphism** onto a currently false principal interval, with an admitted relative inverse. From K use d=¬k_F and α(p)=d∧Ep; F restricted to [0,d] is its inverse by (22). Conversely, given α and an admitted relative inverse β, put

$$
F(q):=\beta(d\land q),
\qquad E(p):=\alpha(p)\lor(\neg d\land p).
\tag{27}
$$

The relative Boolean and admitted-bound laws make F globally Good, with F1=βd=1 and F0=0. The same partition argument makes E Good, and F(Ep)=p while F(¬d)=0. This supplies K with the true proposition ¬d.

Thus the distinction can be read as an embedding-versus-isomorphism question for a false principal interval. Arbitrary relative embeddings do not supply such an isomorphic interval: the [regular-open image-gap example](injective-gap-without-split-kernel.md) verifies C5+J+¬K. That model lacks OS, so the separation-level question OS+J⇒Rev∨K remains open. This description does not invoke an external Schröder–Bernstein theorem or identify an unqualified order-adjoint inverse with a logical isomorphism. The finite relative-generation theorem above supplies a controlled passage to an isomorphic interval under its stated hypothesis.

## 7. Sources

The finite relative-generation condition, controlled selector, same-profile involution, exact separation comparison, one-generator characterization of K and interval interpretations are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The admitted adjoints and their laws are in [Canonical adjoints and image factorization](canonical-adjoints-and-image-factorization.md), §§2–4. Global transversals classify qualified left inverses in [Injective observers and Boolean transversals](injective-observers-and-boolean-transversals.md), §§1–3. The local interval swap and J/K comparison are in [Injective separation decomposition](injective-separation-decomposition.md), §§3–6. Boolean patching and the underlying fixed C framework retain the sources listed in those notes. None supplies a general Choice premise here.
