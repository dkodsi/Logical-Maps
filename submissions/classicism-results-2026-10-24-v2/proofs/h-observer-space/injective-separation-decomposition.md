# Injective separation: reversible witnesses or a true proposition with no image part

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the decomposition and local interval construction: `misc`, this note, §§1–6, unpaginated.

Over C5, injective logical separation has an exact local decomposition. Either reversible observers already separate, or one injective logical observer admits a currently true proposition containing no nonzero image value. That single observer and proposition can then preserve every ordinary observer's current truth profile while making the observer injective.

The result does not prove that injective separation supplies qualified left inverses. It reduces that comparison to a precise one-witness alternative, parallel to the established left-inverse decomposition. The proof uses a local image isomorphism; it never treats the order adjoint of an arbitrary observer as a qualified logical observer.

## 1. Background and the one-observer condition

Work over C5. Fix a finite external qualification list Δ containing t and a relational output type τ. Good_Δ means full Boolean and listed quantifier composite identities, with the established translated equality clauses. Write S_{τ,Δ}[Inj], S_{τ,Δ}[Rev], and S_{τ,Δ}[Good] for separation by currently injective, qualified reversible, and unrestricted Good_Δ observers respectively. The argument agreement for τ ranges over its complete argument tuple.

Use 0,1 for Bottom, Top and p≤q for p∧q=p. For an injective Good_Δ observer E, the admitted canonical adjoints satisfy

$$
L_E\dashv E\dashv R_E,
\qquad L_EE=I=R_EE.
\tag{1}
$$
Put j_E:=ER_E and C_E:=EL_E. The [adjoint theorem](canonical-adjoints-and-image-factorization.md), §§2–4, gives

$$
j_Eq\le q\le C_Eq,
\qquad C_Eq=\neg j_E(\neg q),
\tag{2}
$$
and the Frobenius identity

$$
L_E(q\land Ep)=L_Eq\land p.
\tag{3}
$$
L_E preserves every admitted existential quantifier and binary join; R_E preserves every admitted universal quantifier and binary meet. These are order adjoints, not assumed Boolean observers. All identities between operations below are collected using the Functionality available over C5.

Define

$$
\begin{aligned}
J_\Delta:=\exists E^{tt}c^t\,[
&\mathrm{Good}_\Delta(E)\land\mathrm{Inj}(E)
\land c\\
&\land\forall p^t\,(Ep\le c\to p=0)].
\end{aligned}
\tag{4}
$$
Thus c is currently true, but no nonzero proposition has its E-image below c. By adjunction, the last condition is equivalently R_Ec=0. It does not say that every proposition below c is zero, or that c itself is an image value. No separation premise, inverse or selector occurs in (4).

The main theorem is

$$
\boxed{
S_{\tau,\Delta}[\mathrm{Inj}]
\ \longleftrightarrow\
S_{\tau,\Delta}[\mathrm{Rev}]
\ \lor\
\bigl(S_{\tau,\Delta}[\mathrm{Good}]\land J_\Delta\bigr).
}
\tag{5}
$$
Both disjuncts refer to the same fixed output type and finite qualification list. C5 remains an explicit background throughout.

## 2. One witness normalizes every ordinary truth profile

Suppose E,c witness J_Δ. For an arbitrary admitted Good_Δ observer G, define the admitted lambda term

$$
E_G(p):=(c\land Gp)\lor(\neg c\land Ep).
\tag{6}
$$
Boolean partition patching makes E_G Good_Δ with full composite identities. The fixed coefficient c adds no quantifier type. To prove current injectivity, suppose E_Gp=E_Gq. Restriction to ¬c gives

$$
\neg c\land Ep=\neg c\land Eq,
\qquad E(p\mathbin\triangle q)\le c.
\tag{7}
$$
Condition (4) gives p△q=0 and therefore p=q. This proves Inj(E_G). Equivalently, (7) gives p△q≤R_Ec=0.

Since c is currently true, the entire current truth profile is preserved:

$$
\forall p\,(E_Gp\leftrightarrow Gp).
\tag{8}
$$
The same E,c work for every G. No choice of a family of replacement observers is assumed: (6) is an admitted term in E,c,G. Hence J_Δ plus ordinary separation gives injective separation at every requested relational output type for that same list.

## 3. The canonical local alternative

Fix one injective Good_Δ observer E. Suppress its subscript on L,R,j,C_E and form the admitted proposition

$$
u:=\forall q^t\,(jq\leftrightarrow q).
\tag{9}
$$
An unconditional universal-instantiation theorem, followed by C's Boolean identities, gives

$$
u\land jq=u\land q
\qquad\text{for every }q.
\tag{10}
$$
This is an output identity even when u is false. It is the same discharged logical argument used for the local equalizer in the [left-inverse decomposition](left-inverse-separation-decomposition.md), §3. It does not apply Logical Equivalence to a theorem depending on an optional hypothesis. Applying (10) to ¬q and taking the relative complement inside u gives

$$
u\land C_Eq=u\land q.
\tag{11}
$$
If u is currently false, classical quantifier reasoning supplies q for which jq and q differ in truth. Since jq≤q, q is true and jq false. Put

$$
c:=q\land\neg jq.
\tag{12}
$$
Then c is true. Since j=ER, Boolean preservation by E and RE=I yield

$$
\begin{aligned}
Rc
&=Rq\land R(\neg ERq)\\
&=Rq\land R(E(\neg Rq))\\
&=Rq\land\neg Rq=0.
\end{aligned}
\tag{13}
$$
Thus this very E and c witness J_Δ.

Conversely, any true c with Rc=0 has jc=0, so (9) is false. Therefore J_Δ is equivalently the assertion that **some injective Good_Δ observer's canonical image floor loses the truth of a currently true proposition**. This is a condition on the auxiliary image interior j, not a claim about the language's original necessity operator.

If u is true, (11) instead provides local inverse structure. For every v≤u and every q,

$$
v\land C_E(v\land q)=v\land q.
\tag{14}
$$
Indeed, the left side is at most v∧C_E(u∧q)=v∧q by (11), and the reverse inequality follows from x≤C_Ex. There is no coverage condition C_Ev=1. Thus v need not be a global Boolean transversal of the kind classifying qualified left inverses.

## 4. A true local interval gives a distinguishing involution

Suppose d is currently false, Ed currently true, and u from (9) currently true. Define

$$
v:=u\land Ed\land\neg d,
\qquad a:=Lv,
\qquad r:=\neg(v\lor a).
\tag{15}
$$
The proposition v is true. Since v≤Ed, adjunction gives a≤d. Hence v∧a=0 and v,a,r form a Boolean partition.

Define α(p):=v∧Ep. On the interval below a, α is an admitted relative Boolean isomorphism onto the interval below v, with inverse L restricted to that interval. Here intervals are guarded ranges in the original proposition type, not new object-language types. To verify the assertion, (3) gives

$$
L(v\land Ep)=a\land p,
\tag{16}
$$
while (14) gives

$$
v\land E(L(v\land q))=v\land q.
\tag{17}
$$
For p≤a, (16) is p; every q≤v is recovered by (17). Also v≤C_Ev=Ea, so αa=v. Boolean preservation of E gives all relative Boolean laws for α, including its relative complement law. They transfer to its inverse L on [0,v]. In particular the ambient term q↦L(v∧q) has top a, bottom 0 and satisfies

$$
L(v\land\neg q)=a\land\neg L(v\land q).
\tag{18}
$$
Now patch the two inverse interval maps with identity:

$$
T(p):=(v\land Ep)\lor L(v\land p)\lor(r\land p).
\tag{19}
$$
The three output regions are v,a,r. Their relative Boolean laws prove that T preserves all Boolean operations, fixes 0 and 1, and is an admitted term. This argument uses L only on the local interval; L is not asserted globally Good.

For every σ in the requested list and every admitted H:σt, its middle branch preserves existential quantification:

$$
\begin{aligned}
L(v\land\exists x^\sigma Hx)
&=L(\exists x^\sigma(v\land Hx))\\
&=\exists x^\sigma L(v\land Hx).
\end{aligned}
\tag{20}
$$
The first branch has the same law by E's qualification and fixed-guard distributivity; the identity branch does as well. Distributing the finite outer join through ∃ gives the existential law for T. Its established negation law and quantifier duality give every listed universal law. C5 Functionality collects these output identities into the full composite identities, and the translated equality clauses follow from Boolean qualification over C. Thus T is Good_Δ without adding a type to Δ.

It remains to check the whole inverse equation. Since v≤Ed and v≤¬d,

$$
v\land Ev=0.
\tag{21}
$$
Also v≤Ea and r≤¬a give v∧Er=0. Expanding (19) therefore gives

$$
\begin{aligned}
v\land E(Tp)&=v\land E(L(v\land p))=v\land p,\\
L(v\land Tp)&=L(v\land Ep)=a\land p,\\
r\land Tp&=r\land p.
\end{aligned}
\tag{22}
$$
Equations (19) and (22) yield T(Tp)=p for every p. Functionality gives T∘T=I as a whole-operation identity. Finally, v is true and v≤Ed, so Td is true. T is a qualified involution detecting the originally false d.

Together §§3–4 prove the local alternative: a distinguishing injective observer either yields a distinguishing involution, or supplies the one-observer witness J_Δ. It need not itself have any qualified inverse.

## 5. Separation at the fixed type and list

Assume S_{τ,Δ}[Inj]. Forgetting injectivity gives S_{τ,Δ}[Good]. If reversible separation already holds, the first disjunct of (5) follows.

Otherwise choose X≠Y of output type τ such that every qualified reversible observer agrees on X,Y at every argument tuple. An injective separator E supplies a tuple ā at which E(Xā) and E(Yā) differ in truth. Put

$$
d:=(X\bar a)\mathbin\triangle(Y\bar a).
\tag{23}
$$
Then Ed is true by Boolean preservation. Identity is qualified reversible, so the assumed reversible agreement makes d currently false. Form u as in (9). If u were true, §4 would produce a qualified involution T with Td true. Its Boolean laws would distinguish X,Y at the same tuple, a contradiction. Hence u is false, and §3 proves J_Δ. This gives the second disjunct of (5).

Conversely, reversible separation implies injective separation. The other disjunct supplies injective separation by §2. This proves (5).

In particular,

$$
\neg J_\Delta\ \longrightarrow\
\bigl(S_{\tau,\Delta}[\mathrm{Inj}]
\leftrightarrow S_{\tau,\Delta}[\mathrm{Rev}]\bigr).
\tag{24}
$$
One natural sufficient premise for ¬J_Δ is that every injective Good_Δ observer's image floor preserves current truth. By §3 this premise is also equivalent to ¬J_Δ. Equation (24) concerns separating power, not an identification of the individual injective and reversible classes.

## 6. Comparison with qualified left inverses and full scope

Let K_Δ be the established one-pair condition: admitted Good_Δ observers E,F satisfy F∘E=I, and some currently true c satisfies Fc=0. Then

$$
K_\Delta\ \longrightarrow\ J_\Delta.
\tag{25}
$$
Indeed E is injective, and Ep≤c implies p=F(Ep)≤Fc=0. Thus the same E,c witness (4).

Combining (5) with the earlier [left-inverse decomposition](left-inverse-separation-decomposition.md), §§1–5, gives the following exact comparison over C5 at each fixed τ,Δ:

$$
\begin{array}{rcl}
S_{\tau,\Delta}[\mathrm{Inj}]
&\longleftrightarrow&
S_{\tau,\Delta}[\mathrm{Rev}]
\lor(S_{\tau,\Delta}[\mathrm{Good}]\land J_\Delta),\\
S_{\tau,\Delta}[\mathrm{SplitMono}]
&\longleftrightarrow&
S_{\tau,\Delta}[\mathrm{Rev}]
\lor(S_{\tau,\Delta}[\mathrm{Good}]\land K_\Delta).
\end{array}
\tag{26}
$$
Consequently the remaining injective-to-left-inverse implication is confined to the J_Δ branch: does ordinary separation together with J_Δ force reversible separation or K_Δ? Neither that implication nor J_Δ⇒K_Δ is proved here. The regular-open countermodel in [Boolean transversals](injective-observers-and-boolean-transversals.md), §§4–6, refutes individual qualified splitting but fails OS, so it does not answer this question.

**Update, 24 October 2026, OpenAI Codex.** [A true image gap without a true split kernel](injective-gap-without-split-kernel.md), §§1–5, now refutes J_Δ⇒K_Δ in that same C5 full-function model, using a different observer which even has a qualified left inverse. The model still fails OS, so the separation-level question above remains unresolved. [Finite generation over an observer’s image](finite-relative-image-generation.md), §§3–6, proves the positive finite-relative-generation case and gives exact additional characterizations; the original decomposition proof is unchanged.

There is a stronger finite reformulation at full scope. Over C5, the individual [type-reduction theorem](../modal-selectors-and-quantifier-reduction.md), §4, makes each $\mathrm{Good}_{\{t\}}$ observer Good at every requested finite list. It applies to the same E and, where present, to the same admitted inverse F. Functionality then lifts propositional separation to every relational output type. Consequently, for each of the four qualifications in (26),

$$
\text{full separation schema}
\quad\longleftrightarrow\quad
S_{t,\{t\}}[\text{that qualification}]
\qquad\text{over C5}.
\tag{27}
$$
In particular J_Δ↔$J_{\{t\}}$ and K_Δ↔$K_{\{t\}}$ whenever t∈Δ. One witness qualified at t supplies each requested finite qualification; there is no quantifier over types or infinitely long qualification formula.

Thus the full classifications can be written as genuine finite disjunctions:

$$
\boxed{
\begin{array}{rcl}
\text{full InjSep}
&\longleftrightarrow&
\text{full Rev}\ \lor\
(\text{full OS}\land J_{\{t\}}),\\
\text{full SplitMono}
&\longleftrightarrow&
\text{full Rev}\ \lor\
(\text{full OS}\land K_{\{t\}}),
\end{array}
\qquad\text{over C5}.
}
\tag{28}
$$
Each full-schema expression in (28) is represented by its single closed propositional formula from (27), so no infinitary disjunction is being formed. The current C5 background is essential to this compression. The earlier decomposition over C+BF alone retains its finite-list schema formulation; InjSep itself does not in general imply C5.

## 7. Sources

The one-observer condition, universal-profile normalization, local interval involution and exact decomposition are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The adjoints and their admitted-bound preservation are proved in [Canonical adjoints and image factorization](canonical-adjoints-and-image-factorization.md), §§2–4. The relative Boolean isomorphism and whole quantifier verification refine [Injective observers and Boolean transversals](injective-observers-and-boolean-transversals.md), §§1–3; only local coverage is needed here. The established inverse decomposition is [Left-inverse separation](left-inverse-separation-decomposition.md), §§1–6. Boolean partition patching is in [Logical observer hierarchy](../logical-observer-hierarchy.md), §4. The fixed C framework and its theoremhood restrictions are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §1.5, pp. 16–18; that source supplies the framework, not these new proofs.

 The open separation comparison identified after (26) remains open in this research record.
