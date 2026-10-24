# Separation by the centre of the reversible observer group

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–5, unpaginated.

Requiring a logical observer to commute with every reversible logical observer, while being reversible itself, gives a different restriction from centrality among all logical observers. At full relational schema scope over H, separation by this group centre is exactly C5 together with at most four proposition objects. Equivalently, it is endpoint separation with that finite bound.

The proof uses an admitted proposition measuring where an automorphism moves propositions. Group-central observers fix this proposition. Separation forces every nonidentity automorphism to have total moved support; applying that fact to local interval swaps leaves room for only two Boolean atoms. No external automorphism or unadmitted permutation is introduced.

## 1. The group centre and finite qualification

Fix a finite external list Δ. Write I=λp.p. $\mathrm{Good}_\Delta$ means the full established logical qualification, including its original translated equality clauses as well as the whole Boolean and listed quantifier identities. We do not replace that definition over H by a reduced Boolean/quantifier package. Once C has been recovered, the redundant equality clauses may be derived from Boolean preservation as in the existing observer proofs. Define
$$
\begin{aligned}
\mathrm{Aut}_\Delta(E)
&:=\mathrm{Good}_\Delta(E)\land
 \exists F^{tt}\,[\mathrm{Good}_\Delta(F)
 \land E\circ F=I\land F\circ E=I],\\
\mathrm{ZAut}_\Delta(E)
&:=\mathrm{Aut}_\Delta(E)\land
 \forall G^{tt}\,[\mathrm{Aut}_\Delta(G)
       \to E\circ G=G\circ E].
\end{aligned}
\tag{1}
$$
Every composition equation in (1) is identity of the complete unary operations. The inverse is admitted and has the same qualification. Composition and inversion make the Aut_Δ members a group; the usual calculations use precisely these whole identities. ZAut_Δ is its centre. In particular it quantifies over **all** admitted reversible $\mathrm{Good}_\Delta$ observers, not a chosen abelian subgroup.

Let CentreRevSep(τ,Δ) denote separation at relational output type τ by ZAut_Δ, and CentreRevSep the full schema over relational output types and finite external lists. Since ZAut_Δ implies Aut_Δ, full CentreRevSep implies full Rev, which supplies C5 by the [established reversible-separation theorem](../logical-observer-hierarchy.md), §4. This recovered premise will be used explicitly.

Write
$$
\mathrm{Four}_t:=
\exists u_0u_1u_2u_3\ \forall p\,
 (p=u_0\lor p=u_1\lor p=u_2\lor p=u_3).
\tag{2}
$$
Repetitions are allowed. This bounds proposition objects, not current truth values or an external family of profiles. The local argument in §§2–3 assumes C5, t∈Δ and CentreRevSep(t,Δ). C5 supplies the admitted quantifier order laws and Functionality used below. The full-H conclusion uses only the list {t} for this forward argument.

## 2. Moved support is fixed by the group centre

For any admitted reversible observer G define its moved support by the admitted proposition
$$
m_G:=\exists p^t\,(p\mathbin\triangle Gp),
\tag{3}
$$
where △ is Boolean symmetric difference. Under C5 this existential is the join of its admitted type-t family. It contains every p△Gp. Consequently
$$
m_G=0\quad\longleftrightarrow\quad G=I.
\tag{4}
$$
For the forward direction, each joinand is zero, so Gp=p for every p and Functionality gives the whole identity. The reverse direction evaluates (3) on the constant-zero family.

If Z is a member of ZAut_Δ and G belongs to Aut_Δ, its type-t existential and Boolean laws give
$$
Z(m_G)=\exists p\,(Zp\mathbin\triangle Z(Gp))
       =\exists p\,(Zp\mathbin\triangle G(Zp))
       =m_G.
\tag{5}
$$
The middle equality is centrality. For the last equality, Z is onto by its admitted inverse: each joinand is below m_G, and each r△Gr occurs as a joinand by taking a preimage of that particular r. This proves equality by the two join bounds. It does not choose a preimage uniformly or reindex an external set.

Thus all eligible central reversible observers fix m_G. If m_G is true, their truth profiles agree on m_G and Top; if false, they agree on m_G and Bottom. CentreRevSep(t,Δ) therefore gives
$$
\boxed{m_G=0\ \lor\ m_G=1.}
\tag{6}
$$
Together with (4), every nonidentity reversible $\mathrm{Good}_\Delta$ observer has moved support Top. The conclusion applies to every member of Aut_Δ, including the local swaps constructed next; those swaps need not themselves be central.

## 3. Local swaps force two atoms

Let G belong to Aut_Δ and fix an admitted qualified inverse F. Suppose a≠0 and a∧Ga=0. Put r=¬(a∨Ga) and define
$$
T_a(q):=(Ga\land Gq)\lor(a\land Fq)\lor(r\land q).
\tag{7}
$$
This is an admitted term. It is $\mathrm{Good}_\Delta$ by Boolean partition patching: the three output regions Ga,a,r form a partition of Top, and each branch is a qualified observer on its region. Boolean laws are calculated on the regions; fixed-guard distribution through the listed quantifiers gives their laws. C5 Functionality collects the resulting identities as the full composite identities required by $\mathrm{Good}_\Delta$. This is the same qualified interval-swap construction as in [finite relative generation](finite-relative-image-generation.md), §4, now with the supplied inverse F.

For completeness, the inverse check can be read on the three regions. Applying G or F to (7), the disjointness a∧Ga=0 and the inverse identities give
$$
Ga\land G(T_aq)=Ga\land q,
\qquad a\land F(T_aq)=a\land q,
\qquad r\land T_aq=r\land q.
\tag{8}
$$
For example Ga∧G²a=G(a∧Ga)=0 and Ga∧Gr=0, leaving only Ga∧q in the first expression. The second is its inverse counterpart. Hence T_a²q=q for every q, and Functionality gives T_a∘T_a=I. Thus T_a belongs to Aut_Δ, with itself as admitted qualified inverse.

The operation is identity outside a∨Ga, and T_a(a)=Ga. It follows that
$$
q\mathbin\triangle T_aq\le a\lor Ga\quad\text{for every }q,
\qquad
a\mathbin\triangle T_a(a)=a\lor Ga.
$$
Taking the admitted join proves the exact support equation
$$
m_{T_a}=a\lor Ga.
\tag{9}
$$
Since a≠0, this support is nonzero. Equation (6) now forces a∨Ga=1.

Every nonidentity reversible observer supplies such a pair, after possibly replacing it by its inverse. Indeed choose p with Gp≠p, using Functionality. If p∧¬Gp≠0, take a=p∧¬Gp; then Ga=Gp∧¬G²p is disjoint from a. Otherwise Gp∧¬p≠0; use Gp as the proposition and F as the observer. Rename the resulting observer G and its inverse F. In either case (9) gives
$$
a\ne0,\qquad Ga\ne0,\qquad a\land Ga=0,
\qquad a\lor Ga=1.
\tag{10}
$$
For any 0<b≤a, b and Gb are disjoint, so repeat the same construction at b. Equations (6) and (9) give b∨Gb=1. But Gb≤Ga, and intersecting with a yields
$$
a=a\land(b\lor Gb)=b.
\tag{11}
$$
Therefore a is an atom. The automorphism G makes Ga an atom too. They are complementary by (10), so every proposition q is one of 0,a,Ga,1: distribute q across the two atoms and use their defining minimality. This proves Four_t.

If there is no nonidentity member of Aut_Δ, identity is the only central reversible observer. Separation itself then says that two propositions with the same truth value are identical, so every proposition is Bottom or Top. Four_t holds in this case as well. We have proved the local result
$$
\boxed{
\mathrm{C5}+\mathrm{CentreRevSep}(t,\Delta)
\ \vdash\ \mathrm{Four}_t
\qquad(t\in\Delta).}
\tag{12}
$$
No Boolean Completeness, Zorn, Choice, or unadmitted partial automorphism appears. The argument uses finitely many explicit swaps and the admitted join (3).

## 4. Exact theories and the converse

Under C5, Four_t makes the proposition Boolean algebra atomic. If every proposition is an endpoint, Top is its sole atom. Otherwise choose a nonendpoint a. The four distinct values 0,a,¬a,1 exhaust the domain by Four_t; both a and ¬a are atoms. This proves Atomicity_t directly, with no internal-finiteness or choice principle added.

The established C5+Atomicity_t theorem gives full End and hence full Rev. Moreover every admitted Boolean automorphism in this algebra is identity or interchanges its two atoms. Such operations commute: each is determined on the atoms, and the four-value decomposition and Functionality collect that calculation into a whole commutation identity. If the algebra has only two elements, all its Boolean automorphisms are identity.

Consequently, for **every** finite list Δ, including lists without t, the entire group Aut_Δ is abelian. Every qualified reversible observer is therefore central in that same group. The separating reversible witnesses already supplied by End qualify at their original lists, and give full CentreRevSep. This proves
$$
\boxed{
\mathrm H+\mathrm{CentreRevSep}
\ \equiv\ \mathrm{C5}+\mathrm{Four}_t
\ \equiv\ \mathrm H+\mathrm{Rev}+\mathrm{Four}_t
\ \equiv\ \mathrm H+\mathrm{End}+\mathrm{Four}_t.}
\tag{13}
$$
The forward implication first recovers C5 from full Rev and then uses (12) at {t}. The displayed C5 retains its established type-schema meaning; (13) does not claim that it has become one finitary sentence over H.

An equivalent formulation is full Rev together with pairwise commutativity of **all** qualified reversible observers at each finite list. The forward direction of (13) supplies that commutativity; in the reverse direction it makes the reversible separating class central. A chosen commuting separating subgroup is a different condition: it need not contain the local swaps (7), and the present proof makes no collapse claim for it.

The result is also persistent at full scope:
$$
\boxed{\mathrm{CentreRevSep}
\quad\longleftrightarrow\quad
\Box\mathrm{CentreRevSep}.}
\tag{14}
$$
Here each fixed finite schema instance is boxed separately. To justify the forward implication, first note that C+BF_t proves Four_t→□Four_t. Given witnesses u₀,…,u₃ for (2), NI sends each true identity p=u_i to □(p=u_i). Finite propositional modal reasoning therefore gives ∀p □(∨ᵢp=u_i); BF_t collects this into □∀p(∨ᵢp=u_i). Boxed existential introduction with the displayed witnesses gives □Four_t. No optional finite-enumeration premise is necessitated.

C5 itself persists by 4, instance by instance, since its additional axioms are already boxed. For each requested τ,Δ, discharge the converse proof in (13) as a C theorem from Four_t and its finitely many required C5 instances. Necessitate that theorem and use □Four_t and the necessary C5 instances to obtain □CentreRevSep(τ,Δ). This is a finite argument for each instance; no infinitary conjunction of type qualifications is introduced. The reverse implication in (14) is factivity of □p=(p=Top), already valid in H by equality substitution and truth of Top.

## 5. Position relative to the earlier centrality condition

There are two different centres:

- CentreSep requires Good E commuting with every Good observer.
- CentreRevSep requires reversible Good E commuting with every reversible Good observer.

The latter is not obtained from the former by simply weakening a universal condition: it also requires reversibility of the selected observer. Their full theories are incomparable over H.

The full two-point S5 cluster has C5 and four propositions, so it satisfies CentreRevSep by (13), while it fails ordinary CentreSep by the earlier C5 centrality theorem. The full two-point chain satisfies ordinary CentreSep, including its necessary schema, but fails C5 and therefore fails CentreRevSep. These are the same audited constructions as in [Central logical observers](central-logical-observers.md), §5.

Their conjunction is exactly Extensionality:
$$
\boxed{\mathrm{CentreSep}+\mathrm{CentreRevSep}
\quad\longleftrightarrow\quad\mathrm{Extensionality}.}
\tag{15}
$$
Indeed CentreRevSep supplies C5 and ordinary CentreSep then collapses to Extensionality. Conversely Extensionality makes all Boolean observers identity.

CentreRevSep is strictly weaker than Extensionality and strictly stronger than End. The two-point S5 cluster witnesses the first strictness. A full three-point S5 cluster has End but eight proposition objects, refuting the second converse by (13). CentreRevSep also implies FinBoxSep, since it supplies C5, Rev and a finite proposition domain. No classification of the centre of the native-Box-qualified monoid is asserted by these results.

## 6. Sources

The moved-support argument, local-swap bound, exact theory (13), persistence (14), and comparisons (15) are original ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated.

The fixed C framework and algebraic order are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.3, 1.5 and 2.2, as summarized in the [background](../../source/topics/classicism/background.md). C5's [necessary Barcan consequences](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml) and [Barcan-to-Functionality theorem](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml) provide the stated quantifier and whole-identity background.

The full Rev⇒C5 and C5+Atomicity_t⇒End⇒Rev results are the original observer theorems in [Logical observer separation](../logical-observer-hierarchy.md), §§3–4. The interval-swap qualification is the explicit admitted construction in [Finite relative image generation](finite-relative-image-generation.md), §4. The related invariant-proposition argument is [Reversible separation and fixed propositions](reversible-fixed-proposition-characterization.md), §§1–4; the present restriction is centrality of automorphisms, not invariance of a proposition under all automorphisms.

The earlier centre and its model comparisons are [Central logical observers](central-logical-observers.md), §§4–5, and [Central separation and four propositions](central-separation-and-four-propositions.md), §§2–5. The full S5 examples are standard finite full action models from Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5 and Appendix D, as recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). The new verdicts use those constructions without changing database records or their certificates.
