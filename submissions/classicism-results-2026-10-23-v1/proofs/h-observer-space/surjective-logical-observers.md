# Surjective logical observers have definable qualified right inverses

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the canonical section and kernel characterization: `misc`, this note, §§1–6, unpaginated. Earlier observer results and the C framework are attributed in §7.

Over C5, a surjective logical observer qualified at a finite list containing t has an admitted right inverse qualified at the same list. The inverse is an explicit term built from the fibers and the greatest kernel element. No Choice or independently assumed inverse operation is used.

This identifies surjective logical separation with reversible separation over C5. It also removes the inverse witness from the true-kernel alternative in [the left-inverse decomposition](left-inverse-separation-decomposition.md): that alternative is exactly the existence of one surjective logical observer which sends a currently true proposition to Bottom.

The C5 premise cannot be dropped from the separation equivalence. The [omega-chain shift model](omega-chain-surjective-observers.md) has necessary surjective logical separation while C5 and left-inverse separation fail, even alongside necessary Barcan and necessary propositional Atomicity. Its positive shifts have no admitted right inverse, qualified or otherwise.

## 1. Exact qualifications and ambient theory

Work over C5. Fix a finite external type list Δ with t∈Δ, and let S:tt be an admitted Good_Δ observer. Good_Δ has the full Boolean and quantifier composite identities and translated equality clauses specified in [Qualified right-inverse separation](split-inverse-logical-observers.md), §1.

Surjectivity is the current internal formula

$$
\operatorname{Onto}(S):=\forall q^t\,\exists p^t\,[Sp=q].
\tag{1}
$$
It ranges over admitted proposition objects and asserts output identities. It is not external surjectivity on some larger collection of possible values. We assume (1), not an admitted choice of its witnesses. All constructions below are lambda terms in S.

C5 supplies the Barcan and Functionality instances used to collect output identities into whole-operation identities. It also makes every equality judgment an endpoint: a true equality is Top, and a false equality is Bottom. Thus S fixes every equality judgment occurring below, because its Boolean laws fix the endpoints. No extra equality-fixing qualification is imposed on S.

Write x≤y for x∧y=x. Quantifiers in C+BF are greatest or least bounds of their admitted families in this Boolean order. Only admitted families are used; no completeness for arbitrary external subsets is claimed. This order reading and the fixed-guard quantifier identities are the existing C+BF calculations used in [meet/quantifier separation](../meet-quantifier-separation.md) and [logical Boolean patching](../logical-observer-hierarchy.md), §4.

## 2. The greatest kernel element

Define the admitted proposition

$$
k_S:=\exists p^t\,[(Sp=\bot)\land p].
\tag{2}
$$
Since t∈Δ, existential preservation and equality-judgment fixing give

$$
\begin{aligned}
Sk_S
&=\exists p\,S((Sp=\bot)\land p)\\
&=\exists p\,[(Sp=\bot)\land Sp]
=\bot.
\end{aligned}
\tag{3}
$$
The last equality is an unconditional C logical identity: each displayed conjunction is contradictory by equality substitution. It is not obtained by necessitating the optional qualification of S.

If Sp=Bottom, its equality judgment is Top. The p-instance in (2) is then p itself, so p≤k_S. Conversely p≤k_S implies Sp≤Sk_S=Bottom. Therefore

$$
Sp=\bot\quad\longleftrightarrow\quad p\le k_S.
\tag{4}
$$
Thus the entire kernel is the principal ideal below the explicitly admitted k_S. Surjectivity has not yet been used.

Put a:=¬k_S. S is injective on the interval [Bottom,a]. Indeed, if x,y≤a and Sx=Sy, Boolean preservation gives S(x△y)=Bottom. By (4), x△y≤k_S, whereas x△y≤a. Hence x=y. Here △ is the Boolean symmetric difference available in C.

## 3. A canonical representative in each fiber

Define

$$
j_S(q):=\exists p^t\,[(Sp=q)\land p],
\qquad
r_S(q):=a\land j_S(q).
\tag{5}
$$
These are admitted tt terms. Applying S to j_S(q) gives

$$
S(j_S(q))=\exists p\,[(Sp=q)\land Sp]=q.
\tag{6}
$$
For the last identity, every joinand is below q by equality substitution. Surjectivity supplies an admitted p₀ with Sp₀=q; its equality judgment is Top, so its joinand is q. The two inequalities prove equality. This uses a witness only in the proof for the given q; the term in (5) was defined before choosing any witness.

Since Sa=Top by (3), equations (5)–(6) give

$$
r_S(q)\le a,\qquad S(r_S(q))=q.
\tag{7}
$$
The injectivity on [Bottom,a] proved in §2 shows that r_S(q) is the unique representative in that interval having S-image q. In particular,

$$
r_S(\bot)=\bot,\qquad r_S(\top)=a.
\tag{8}
$$
Uniqueness and Boolean preservation by S give the relative Boolean laws

$$
\begin{aligned}
r_S(p\land q)&=r_Sp\land r_Sq,\\
r_S(p\lor q)&=r_Sp\lor r_Sq,\\
r_S(\neg p)&=a\land\neg r_Sp.
\end{aligned}
\tag{9}
$$
For each equation, both candidates lie below a and applying S gives the same proposition. The complement in (9) is explicitly the relative complement below a. We do not treat r_S itself as an endpoint-fixing observer of the original Boolean algebra.

## 4. Quantifiers and the qualified right inverse

Fix σ∈Δ and any admitted predicate G:σt. Both

$$
r_S(\forall x^\sigma Gx)
\quad\text{and}\quad
\forall x^\sigma r_S(Gx)
$$
lie below a. For the second, choose an admitted σ-object and use universal instantiation; the type domains are inhabited in the fixed framework. Applying S to either expression gives ∀x Gx, using S's full Q_σ law and (7). The uniqueness from §3 therefore proves

$$
r_S(\forall x^\sigma Gx)=\forall x^\sigma r_S(Gx).
\tag{10}
$$
For the existential version, every r_S(Gx) lies below a, so its admitted join also lies below a. Apply S's P_σ law and the same uniqueness argument to obtain

$$
r_S(\exists x^\sigma Gx)=\exists x^\sigma r_S(Gx).
\tag{11}
$$
The pointwise identities S(r_S(Gx))=Gx are collected into the required predicate identity using C5 Functionality. Likewise the identities in (9)–(11), universally over their admitted inputs, can be collected into their whole composite forms. No optional current-surjectivity premise is necessitated.

Now fill the complementary region with identity:

$$
E_S(q):=r_S(q)\lor(k_S\land q).
\tag{12}
$$
This is an admitted tt term. The relative Boolean laws (8)–(9) and the partition a,k_S give the ordinary Boolean laws for E_S, including E_S(Top)=Top and E_S(Bottom)=Bottom.

For a listed quantifier, rewrite the right side of (12) as

$$
(a\land r_S(q))\lor(k_S\land q).
$$
The fixed-guard universal distribution identity gives

$$
\begin{aligned}
\forall x\,E_S(Gx)
&=(a\land\forall x\,r_S(Gx))
  \lor(k_S\land\forall x\,Gx)\\
&=r_S(\forall x\,Gx)
  \lor(k_S\land\forall x\,Gx)\\
&=E_S(\forall x\,Gx).
\end{aligned}
\tag{13}
$$
The existential calculation uses the corresponding distribution identity and (11). These are the C identities for fixed propositional guards, not arbitrary exchanges of external infima. C5 Functionality collects the resulting preservation equations into the full composite operation identities. The translated equality clauses then follow from Boolean qualification over C. Hence E_S is Good_Δ for the original list.

Finally, (3) and (7) give

$$
S(E_Sq)=S(r_Sq)\lor(Sk_S\land Sq)=q.
\tag{14}
$$
Functionality at tt yields the whole-operation identity

$$
S\circ E_S=I.
\tag{15}
$$
This is the promised qualified right inverse. The use of Q_t/P_t in the construction explains the requirement t∈Δ. Each other σ∈Δ is preserved by its own calculation; no further observer quantifier type is introduced.

## 5. Surjective separation and reversible separation

The converse to the construction is immediate: an admitted right inverse gives current surjectivity by evaluating its whole inverse identity at any q. Thus, over C5 and at each finite Δ containing t,

$$
\boxed{\operatorname{Good}_\Delta(S)\land\operatorname{Onto}(S)
\quad\longleftrightarrow\quad
\operatorname{SplitEpi}_\Delta(S).}
\tag{16}
$$
This time it is an equality of the individual qualified classes, not merely their separating power. The right inverse is admitted and qualified; current injectivity of S is not assumed.

The existing same-list right-inverse patching theorem over C+BF identifies SplitEpi separation with reversible separation. Combining it with (16), for every relational output type τ,

$$
\boxed{
S_{\tau,\Delta}[\operatorname{Good}\land\operatorname{Onto}]
\quad\longleftrightarrow\quad
S_{\tau,\Delta}[\operatorname{Rev}]
\qquad\text{over C5, }t\in\Delta.
}
\tag{17}
$$
For the full schema, enlarge each requested finite list by t and weaken back as needed. Therefore full surjective-logical separation together with C5 is exactly full Rev over H. The explicit C5 premise is retained in this formulation. This argument does not claim that surjective-logical separation alone recovers C5, or that current surjectivity over bare C supplies the same qualified section.

The section need not be a left inverse of S. Equation (4) shows that S is injective exactly when k_S=Bottom; in that special case a=Top and the relative inverse already gives both whole inverse equations. A kernel proposition that is currently false may nevertheless be nonbottom. Current falsity of k_S must not be confused with injectivity.

## 6. The true-kernel alternative without an inverse parameter

Recall K_Δ from [Left-inverse separation decomposition](left-inverse-separation-decomposition.md), §1:

$$
K_\Delta:=\exists E,F,c\,[
\operatorname{Good}_\Delta(E)\land\operatorname{Good}_\Delta(F)
\land F\circ E=I\land c\land Fc=\bot].
$$
Over C5, for finite Δ containing t, it has the equivalent formulations

$$
\boxed{
\begin{aligned}
K_\Delta
&\longleftrightarrow
\exists S\,[\operatorname{Good}_\Delta(S)
\land\operatorname{Onto}(S)\land k_S]\\
&\longleftrightarrow
\exists S,c\,[\operatorname{Good}_\Delta(S)
\land\operatorname{Onto}(S)\land c\land Sc=\bot].
\end{aligned}}
\tag{18}
$$
For the forward direction set S=F. The given right inverse makes S onto, and (4) gives c≤k_S, so k_S is true. Conversely, use E_S from (12) and c=k_S; equations (3) and (15) witness K_Δ. The last equivalence is again (3)–(4). Thus k_S depends only on the surjective observer, not on a chosen section.

Since Sc=Bottom is equivalent over C to □¬Sc, one may also read the last line of (18) as the existence of a surjective qualified observer and a currently true c for which Sc is necessarily false. Equivalently, ¬K_Δ says that every such S satisfies ∀c(c→◇Sc). This is a modal characterization using only admitted observers and proposition parameters, with no quantified inverse witness.

Substituting (18) into the fixed-instance decomposition gives the exact conditional statement over C5+□OS: SplitMono separation at the requested output type and list is equivalent to either reversible separation at that instance or the existence of a surjective qualified observer with a currently true maximal kernel element. The present result proves the admission of a qualified section once surjectivity is given. The later [linear and circular fibre model](linear-circular-fibre-left-inverse-gap.md), §§5–9, satisfies C5+□OS but fails SplitMono at its explicit finite list Δ₀. Hence both alternatives fail there: necessary ordinary separation need not supply such a surjective observer.

## 7. Sources

The canonical admitted kernel, relative fiber representative, qualified right-inverse term and observer consequences are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The Good qualification and same-list right-inverse separation theorem are [Qualified right-inverse separation](split-inverse-logical-observers.md), §§1–4. The true-kernel separation decomposition is [Left-inverse separation](left-inverse-separation-decomposition.md), §§1–6. Their arguments have direct source `misc` and retain their stated backgrounds. The Boolean fixed-guard calculation is in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §4.

C, Intensionality and the modal interpretation of identity are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §1.5, pp. 16–18. The C5-to-Barcan and Barcan-to-Functionality consequences are recorded in [necessary distinctness implies necessary Barcan](../../source/topics/classicism/results/necessary-distinctness-necessary-r-implies-necessary-barcan-r.yaml) and [Barcan implies Functionality](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml). These sources supply the background, not the new section construction.

 No general choice principle, external section, or arbitrary external-family completeness is asserted.
