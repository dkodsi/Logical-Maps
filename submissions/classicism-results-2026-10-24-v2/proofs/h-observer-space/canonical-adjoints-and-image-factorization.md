# Canonical order adjoints and the image of a logical observer

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new constructions and characterizations: `misc`, this note, §§2–7, unpaginated.

Every logical observer qualified at t over C5 has two admitted order adjoints, whether or not it is injective or surjective. They give a canonical kernel/image factorization and exact tests for injectivity, surjectivity and reversibility. Filling the kernel part with identity produces two endpoint-fixing operators, one preserving meet and every universal quantifier, the other preserving join and every existential quantifier. They coincide exactly when the original observer is onto, recovering its qualified right inverse.

The image also has an admitted floor and ceiling. Its floor is an auxiliary S5 interior operator; it is the original necessity operation exactly when the observer is endpoint-valued. The auxiliary operator must otherwise be kept separate from the language's fixed Box. Commutation with the original Box gives a different exact condition: injectivity of the Boolean observer.

## 1. Assumptions and what was already known

Work over C5 in the fixed relational type system. Write 0,1 for Bottom, Top, and x≤y for the output identity x∧y=x. Let $E^{tt}$ be an admitted $\mathrm{Good}_{\{t\}}$ observer: it has the full Boolean and type-t quantifier composite identities. Equivalently, one can begin with Good_Δ for any fixed finite external list containing t. No injectivity, surjectivity, inverse or choice assumption is imposed on E.

C5 supplies the Barcan and Functionality instances used below. In particular:

- every identity judgment is an endpoint, Top when true and Bottom when false;
- a Boolean observer fixes such a judgment, including the identity expressing x≤y;
- ∀ and ∃ give the greatest lower and least upper bounds of their admitted families in the Boolean order;
- universally proved output identities can be collected into whole-operation identities by Functionality.

Only admitted families occur. No assertion is made that arbitrary external subsets of the proposition domain have bounds. All definitions in this note are lambda terms in E and their displayed proposition parameters.

The individual-observer result

$$
\mathrm{Good}_{\{t\}}(E)
\quad\Longrightarrow\quad
\mathrm{Good}_{\Delta}(E)
\text{ for every fixed finite external }\Delta
\tag{1}
$$
was already proved by range coding in [Modal selectors and quantifier reduction](../modal-selectors-and-quantifier-reduction.md), §4. Section 2 below gives an alternative proof through the new admitted adjoints. Equation (1) is therefore a recovered result, not a new type-collapse claim. It concerns the same E at each requested finite list; it does not introduce an infinitary qualification formula or an object-language type quantifier.

The earlier [canonical-section theorem](surjective-logical-observers.md), §§2–4, constructed the maximal kernel and a qualified right inverse under surjectivity. The present argument retains that kernel, constructs adjoints without surjectivity, and identifies exactly which further laws recover the section.

## 2. The admitted adjunctions

Define

$$
R(q):=\exists p^t\,[(Ep\le q)\land p],
\qquad
L(q):=\neg R(\neg q).
\tag{2}
$$
The order guard Ep≤q abbreviates an identity judgment. C5 makes it an endpoint, so E fixes it. Type-t existential preservation therefore gives

$$
E(Rq)=\exists p\,[(Ep\le q)\land Ep]\le q.
\tag{3}
$$
For the inequality, each joinand is 0 when its guard is false and is Ep≤q when its guard is true. Conversely, if Ep≤q, the p-joinand in (2) is p, and hence p≤Rq. Monotonicity of E and (3) prove

$$
\boxed{Ep\le q\quad\longleftrightarrow\quad p\le Rq.}
\tag{4}
$$
Boolean complementation gives the dual adjunction:

$$
\begin{aligned}
Lq\le p
&\longleftrightarrow \neg p\le R(\neg q)\\
&\longleftrightarrow E(\neg p)\le\neg q\\
&\longleftrightarrow q\le Ep.
\end{aligned}
\tag{5}
$$
Thus L is left adjoint to E, and R is right adjoint to E. These are order adjoints. Neither is being presumed to be a Boolean observer or an inverse.

**Admitted-family preservation.** R preserves every admitted meet, and L preserves every admitted join, regardless of the input family's type. For example, if F:σt is admitted, then for any p,

$$
\begin{aligned}
p\le R(\forall x^\sigma Fx)
&\longleftrightarrow Ep\le\forall x^\sigma Fx\\
&\longleftrightarrow\forall x^\sigma\,(Ep\le Fx)\\
&\longleftrightarrow\forall x^\sigma\,(p\le R(Fx))\\
&\longleftrightarrow p\le\forall x^\sigma R(Fx).
\end{aligned}
\tag{6}
$$
Antisymmetry gives equality of the two outputs. The dual argument proves L(∃x Fx)=∃x L(Fx). The same adjunction calculations show that E, as a left adjoint, preserves all admitted joins, and as a right adjoint preserves all admitted meets. Consequently E has every requested quantifier law. C5 Functionality gives the full λF identities, and the translated equality clauses follow from Boolean qualification over C. This proves (1) again.

In particular R preserves binary meet and 1; L preserves binary join and 0. These include the whole binary operation identities by Functionality. The argument used no enumeration of an image, no external completeness and no selected preimages.

## 3. The kernel and canonical image representatives

Put

$$
k:=R0,\qquad a:=\neg k.
\tag{7}
$$
Equations (3)–(4) give

$$
Ek=0,
\qquad
Ep=0\quad\longleftrightarrow\quad p\le k.
\tag{8}
$$
This k is the greatest kernel proposition from the earlier canonical-section theorem. The guard Ep≤0 is equivalent to Ep=0; both guards are endpoints, so their terms in the admitted join agree. Boolean preservation also gives Ea=1.

For any x,p,

$$
\begin{aligned}
Ex\le Ep
&\longleftrightarrow E(x\land\neg p)=0\\
&\longleftrightarrow x\land\neg p\le k\\
&\longleftrightarrow x\le p\lor k.
\end{aligned}
\tag{9}
$$
Combining (9) with (4), and then taking Boolean duals, yields

$$
\boxed{R(Ep)=p\lor k,\qquad L(Ep)=p\land a.}
\tag{10}
$$
The exact fiber and order conditions are

$$
\begin{aligned}
Ep=Eq&\longleftrightarrow p\land a=q\land a,\\
Ep\le Eq&\longleftrightarrow p\land a\le q\land a.
\end{aligned}
\tag{11}
$$
The second is (9) rewritten by the Boolean partition a,k, and the first follows by applying it in both directions. Thus E is injective on [0,a].

Define the normalized right adjoint and image predicate by

$$
r(q):=a\land Rq,
\qquad
\mathrm{Im}_E(q):=\exists p\,(Ep=q).
\tag{12}
$$
These are admitted terms. Since k≤Rq by monotonicity,

$$
Rq=k\lor r(q),\qquad
R1=1,\quad L0=0,\quad L1=a,
\quad r0=0,\quad r1=a.
\tag{13}
$$
Both r(q) and Lq lie in [0,a]. For an image value q=Ep, equation (10) gives

$$
r(q)=Lq=p\land a.
\tag{14}
$$
This is the unique representative of q in [0,a]. Accordingly E factors explicitly as

$$
p\longmapsto p\land a
\longmapsto E(p\land a)=Ep,
\tag{15}
$$
where the second map, restricted to [0,a], is a Boolean order isomorphism onto the image. Its admitted inverse on that image is r, equivalently L. The interval uses relative top a and relative complement a∧¬p. No new object-language type for the interval or image is asserted; the isomorphism is expressed by the displayed terms and restricted quantifiers.

The image is closed under every admitted quantifier family whose values lie in it. To see this without Choice, let F:σt and suppose Im_E(Fx) for every x. Then E(L(Fx))=Fx by (14). The admitted family λx.L(Fx) is a uniform lift, and E's quantifier preservation gives

$$
E(\forall x\,L(Fx))=\forall x\,Fx,
\qquad
E(\exists x\,L(Fx))=\exists x\,Fx.
\tag{16}
$$
Hence both outputs lie in the image. The interval [0,a] is likewise closed under its admitted inhabited meets and joins; all types in the framework are inhabited. The factorization respects the relative Boolean operations and these quantifiers as output identities under the indicated interval/image guards. No higher-type object with an unintroduced interval or image as its domain is asserted. For the actual ambient tt terms, putting m_a:=λp.a∧p gives the whole identities E∘m_a=E and r∘E=L∘E=m_a by (10)–(15) and Functionality.

## 4. The image floor and ceiling

Define the admitted operators

$$
j:=E\circ R,
\qquad c:=E\circ L.
\tag{17}
$$
For every q, j(q) is the greatest image element below q. Indeed j(q)≤q by (3). If Ep≤q, then p≤Rq, so Ep≤j(q). Dually c(q) is the least image element above q, by (5). In particular

$$
j(q)\le q\le c(q),
\tag{18}
$$
$$
\mathrm{Im}_E(q)
\longleftrightarrow j(q)=q
\longleftrightarrow c(q)=q.
\tag{19}
$$
The range of each of j,c is exactly the image of E. The floor and ceiling properties give

$$
j^2=j,\qquad c^2=c,\qquad
j\circ c=c,\qquad c\circ j=j,
\qquad c(q)=\neg j(\neg q).
\tag{20}
$$
Here, as throughout, the operator equations are whole identities supplied by C5 Functionality after the output calculations. Since E and R preserve admitted meets, j preserves them; c preserves admitted joins. Also j0=0,j1=1,c0=0,c1=1.

Thus j is an **auxiliary S5 interior operator** on the Boolean proposition algebra: it preserves meet and 1, is below identity, is idempotent, and fixes every value of its dual closure c. These are algebraic identities for the new admitted operator j. They are not new axioms for the language's original necessity operation, nor is j automatically a full Boolean observer.

The normalized adjoints satisfy

$$
r(q)\le Lq.
\tag{21}
$$
For E(rq)=j(q)≤c(q)=E(Lq), and both arguments lie in [0,a], where E reflects order by (11). Equality holds precisely at the image values:

$$
r(q)=Lq\quad\longleftrightarrow\quad\mathrm{Im}_E(q).
\tag{22}
$$
The forward direction combines (18) with equality of the two E-images; the reverse is (14).

There is also an exact test for idempotence of the original observer:

$$
\boxed{E\circ E=E\quad\longleftrightarrow\quad
\forall q\,[j(q)\le Eq\le c(q)].}
\tag{23}
$$
If E is idempotent it fixes its image; applying E to (18) proves the inequalities. Conversely, take q=Ep. Both image approximations of q equal q, so the inequalities force E(Ep)=Ep. Functionality supplies the whole identity.

## 5. Exact preservation tests for injection, surjection and inverses

Use M,V,N for full preservation of meet, join and negation. In the following table the one-place endpoint equations are ordinary output identities; R=L and all preservation laws can be read as whole-operation identities.

| Property of E | Equivalent adjoint conditions |
|---|---|
| E is injective | k=0; R0=0; L1=1; R∘E=I; L∘E=I |
| E is onto | j=I; c=I; r=L; V(R); M(L) |
| E is bijective | R=L; N(R); N(L); R is a qualified logical observer; L is a qualified logical observer |

Each entry in a row is equivalent to the property in the first column.

**Injectivity.** Equations (8), (10) and (11) prove the first row. For example, an injective E sends k and 0 to the same output only if k=0; conversely k=0 makes (11) reflect equality on the whole domain.

**Surjectivity.** Equation (19) proves the equivalences with j=I and c=I, and (22) proves the equivalence with r=L.

If R preserves binary joins, then

$$
j(q)\lor j(\neg q)
=E(Rq\lor R(\neg q))
=E(R1)=1.
\tag{24}
$$
The two terms lie below q and ¬q respectively. Boolean distributivity therefore gives j(q)=q, and E is onto.

Conversely suppose E is onto. The restriction E:[0,a]→Im(E) is now an isomorphism onto the entire proposition algebra, with inverse r. Uniqueness of representatives makes r preserve relative joins. Since Rq=k∨r(q), R preserves binary joins too. Boolean duality gives the equivalence with meet preservation by L.

Notice that V(R) does not make R a Boolean observer when k≠0: its Bottom value is then k. The onto condition and the endpoint-fixing condition occupy different rows.

**Bijectivity.** If R=L, evaluating at 0 gives k=0, while r=R=L gives surjectivity. If E is bijective, (10) and (19) make both R and L its two-sided inverse, so they are equal. By definition Lq=¬R(¬q), their equality is precisely negation preservation by R, and equivalently by L.

When E is bijective, the common inverse preserves all admitted meets because it is R and all admitted joins because it is L. It preserves negation and both endpoints, so it is a qualified logical observer at every requested finite type list. Conversely any such qualification includes negation preservation, so the table gives bijectivity. This proves the inverse statement with explicit admitted terms and without Choice.

The table concerns individual observers. In particular, an order adjoint fixing both endpoints is not thereby a Boolean inverse: that condition gives injectivity, while join or meet preservation in the second row supplies the additional surjectivity. A restriction requiring a qualified adjoint selects exactly the reversible individual observers over this base.

## 6. Canonical endpoint-fixing envelopes

Define

$$
T^-(q):=r(q)\lor(k\land q),
\qquad
T^+(q):=Lq\lor(k\land q).
\tag{25}
$$
These are admitted terms before any onto assumption. They satisfy

$$
T^-0=T^+0=0,\qquad T^-1=T^+1=1,
\qquad T^-q\le T^+q,
\tag{26}
$$
$$
T^+(q)=\neg T^-(\neg q),
\qquad E\circ T^-=j,
\qquad E\circ T^+=c.
\tag{27}
$$
The endpoint equations follow from (13), the inequality from (21), and the duality from Lq=¬R(¬q) together with the partition a,k. Applying E kills the k-part and gives (27).

The operator r preserves binary meets and all admitted universal quantifiers, with relative top a. For the latter,

$$
r(\forall x\,Fx)
=a\land\forall x\,R(Fx)
=\forall x\,(a\land R(Fx)).
\tag{28}
$$
The last identity uses the fixed-guard quantifier law and the inhabited input type. L preserves binary joins and all admitted existential quantifiers, with relative top a. Patching each with identity on the complementary region k therefore gives:

- T^- preserves whole meet and every whole universal-quantifier operation;
- T^+ preserves whole join and every whole existential-quantifier operation.

For example, the partition identity gives

$$
\begin{aligned}
\forall x\,T^-(Fx)
&=(a\land\forall x\,r(Fx))
  \lor(k\land\forall x\,Fx)\\
&=r(\forall x\,Fx)\lor(k\land\forall x\,Fx)
=T^-(\forall x\,Fx).
\end{aligned}
\tag{29}
$$
These are the existing C fixed-guard Boolean and quantifier identities, not arbitrary external-infimum exchanges. Functionality collects the equations into the full composite identities.

Moreover,

$$
\boxed{
E\text{ onto}\quad\longleftrightarrow\quad
T^-=T^+\quad\longleftrightarrow\quad
V(T^-)\quad\longleftrightarrow\quad N(T^-).}
\tag{30}
$$
The dual conditions M(T^+) and N(T^+) are equivalent as well. To see the first equivalence, intersect the equality T^-=T^+ with a and use (22). For the others, an endpoint-fixing meet/join homomorphism of Boolean algebras preserves complements, by uniqueness of complements. Negation preservation identifies T^- with its dual T^+ in (27). Conversely their equality combines the two displayed preservation halves.

When these equivalent conditions hold, their common value T is a fully qualified observer at every requested finite list, and E∘T=I by (27). On every image value, r agrees with the unique relative fiber representative in [Surjective logical observers](surjective-logical-observers.md), §§3–4. Under onto, every input is such a value, so (25) recovers exactly that canonical qualified right inverse. The current construction supplies its two distinct one-sided envelopes even when E is not onto.

## 7. Endpoint observers and the original necessity operation

Write $\Box_t:=\lambda q.(q=1)$ for the fixed necessity operation, and $\Diamond_t:=\lambda q.(q\ne0)$. Over C5 their outputs are endpoints. In particular

$$
\Box_t(q)=
\begin{cases}
1& q=1,\\
0& q\ne1.
\end{cases}
\tag{31}
$$
No case-function admission is inferred from this notation: Box_t is the already admitted identity-judgment term.

**Theorem.** For the original observer E,

$$
\boxed{
\forall p\,(Ep=0\lor Ep=1)
\quad\longleftrightarrow\quad j=\Box_t
\quad\longleftrightarrow\quad c=\Diamond_t.}
\tag{32}
$$
**Proof.** If E is endpoint-valued, its image is exactly {0,1}, since it fixes both endpoints. Its image floor j sends 1 to 1. For q≠1, the only image element below q is 0: if 1≤q then q=1. Thus j has the values (31), and Functionality gives j=Box_t.

Conversely, suppose j=Box_t. Every Ep lies in the image and is fixed by j. Hence Ep=Box_t(Ep), whose right side is an endpoint. This makes E endpoint-valued. Equivalently, the fixed points of Box_t are precisely 0 and 1, which is exactly the image by (19).

Finally c(q)=¬j(¬q), and over C5 the complement-dual of the endpoint test (31) is Diamond_t: it is 0 exactly at q=0 and 1 otherwise. Functionality gives the full dual operation identity and the remaining equivalence. ∎

This identifies exactly one special case of the auxiliary modality. In general the image of E can be larger, and j need not be the original Box. At the other extreme, j=I holds exactly when E is onto. The auxiliary construction supplies neither a new theorem about native modal strength nor a general claim that every admitted S5 interior is the image floor of a logical observer.

**Native modal commutation.** There is a separate exact characterization, which requires only Boolean qualification of E over C5, not the type-t quantifier law:

$$
\boxed{
E\text{ injective}
\quad\longleftrightarrow\quad
E\circ\Box_t=\Box_t\circ E
\quad\longleftrightarrow\quad
E\circ\Diamond_t=\Diamond_t\circ E.}
\tag{33}
$$
E fixes every Box_t(q), because it is an endpoint. Box commutation is therefore equivalent to Box_t(Eq)=Box_t(q) for every q. By (31), and since E1=1, this is precisely reflection of Top: Eq=1 implies q=1. An injective Boolean E reflects Top. Conversely, if E reflects Top and Ep=0, then E(¬p)=1 forces ¬p=1 and p=0. Thus its Boolean kernel is trivial, and Ep=Eq implies E(p△q)=0 and hence p=q. This proves the first equivalence without using R or a maximal-kernel term.

For Diamond, endpoint fixing similarly reduces commutation to Diamond_t(Eq)=Diamond_t(q). Since E0=0, this is reflection of Bottom, equivalent by the same Boolean argument to injectivity. Functionality supplies both whole composite equations. This is an individual-observer characterization; no additional separation-class implication is asserted here. In particular, fixing every necessity judgment and commuting with necessity are different conditions: the former holds for every Boolean E over C5, whereas (33) imposes injectivity.

## 8. Sources, novelty and limits

The admitted adjoints, exact preservation table, image floor/ceiling, idempotence test, one-sided envelope construction, endpoint characterization and native-modal commutation criterion are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§2–7, unpaginated.

The all-type qualification consequence was already established in [Modal selectors and quantifier reduction](../modal-selectors-and-quantifier-reduction.md), §4; the present adjunction gives a different proof of that same result. The kernel and surjective relative representative are from [Surjective logical observers](surjective-logical-observers.md), §§2–4. The new envelopes extend that construction to observers which are not onto. The Boolean fixed-guard quantifier identities are used as in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §4.

The fixed framework is [the topic background](../../source/topics/classicism/background.md). C5-to-Barcan and Barcan-to-Functionality are the recorded results [necessary distinctness implies necessary Barcan](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml) and [Barcan implies Functionality](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml): Bacon and Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.3, p. 22, and Proposition 2.1, n. 27, pp. 20–21, respectively. Those sources supply the background, not the new adjoint construction.

Every quantified family and every constructed operator is admitted. Finite lists and type choices remain external schema parameters. No arbitrary external completeness, Choice principle or necessitation of optional premises is used.
