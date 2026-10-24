# Central separation, four propositions and persistence

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–5, unpaginated.

Central logical separation forces the proposition algebra to be finite, with at most two Boolean atoms. More exactly, over H it is equivalent to idempotent native-Box separation together with at most four proposition objects. It also implies its separately boxed schema. These results do not assume C5.

The key step is a greatest-kernel construction for qualified idempotents that avoids the C5 equality guards used in the general adjoint construction. It lets the earlier centre argument proceed over C with the Barcan and Functionality consequences already supplied by full separation.

## 1. A kernel for idempotent observers without C5

Use the whole-operation qualifications and centrality from [Central logical observers](central-logical-observers.md), §1:
$$
\mathrm{Cent}_\Delta(E):=
\mathrm{Good}_\Delta(E)\land
\forall G^{tt}[\mathrm{Good}_\Delta(G)
 \to E\circ G=G\circ E].
\tag{1}
$$
The finite external list Δ will contain t whenever the kernel construction below is used. Good includes the whole Boolean and listed quantifier identities. Composition equality means identity of the complete unary operations. Centrality quantifies over all admitted Good observers at that list, not merely a chosen commuting family.

The local calculations first take place over C, with unary Functionality when output equations are collected into whole identities. Full CentreSep over H implies full OS and therefore supplies C, BF and Functionality by the [typed separation theorem](typed-separation-and-classicism.md). These consequences will remain explicit in the later modal step.

The Boolean-patch proof in the central note, §2, gives E²=E for a central E. In fact the following construction works for any idempotent $\mathrm{Good}_\Delta$ observer E with t∈Δ. Write p△q for Boolean symmetric difference, and define
$$
k_E:=\exists p^t\,(p\mathbin\triangle Ep).
\tag{2}
$$
This is an admitted proposition. Existential preservation at t and idempotence give
$$
Ek_E=\exists p\,(Ep\mathbin\triangle E^2p)=0.
\tag{3}
$$
Every p△Ep is below k_E by the unconditional existential-introduction identity of C. Thus Ep=0 implies p≤k_E. The converse follows from Boolean monotonicity and (3), so
$$
\boxed{Ep=0\quad\longleftrightarrow\quad p\le k_E.}
\tag{4}
$$
In particular k_E is the greatest kernel element. Also
$$
\neg k_E\land Ep=\neg k_E\land p.
\tag{5}
$$
Equation (3) uses the assumed whole P_t law and the whole idempotence identity directly. No optional equivalence is promoted to identity or necessity. Unlike the general C5 kernel formula, (2) contains no equality-valued selection guard; no necessity-of-distinctness premise is needed.

## 2. The centre and the four-value bound

Assume C, the available unary Functionality, t∈Δ and ordinary propositional separation S_{t,Δ}. Let E be central and put k=k_E. The argument of the earlier centre classification now uses (4) in place of its C5 kernel theorem.

For every $\mathrm{Good}_\Delta$ observer G, commutation gives E(Gk)=G(Ek)=0, hence Gk≤k. If k is currently false, every Gk is false, so separation from 0 gives k=0. A Boolean observer with zero kernel is injective; injectivity and E²=E give E=I.

If k is currently true, commute E with the admitted patch
$$
P_k(G,I)(p):=(k\land Gp)\lor(\neg k\land p).
\tag{6}
$$
Since Ek=0, the resulting identity gives k∧G(Ep)=k∧Ep. Thus G(Ep) has the same current truth as Ep for every Good G. Ordinary separation compares Ep with 1 when it is true and with 0 when it is false. Therefore every Ep is an endpoint.

Two endpoint-valued Boolean observers E,F satisfy E∘F=F and F∘E=E, since they fix both endpoints. They commute only if E=F. We have consequently proved the C5-free local classification:
$$
\boxed{
\text{Every central observer is }I
\text{ or one endpoint observer with currently true greatest kernel.}}
\tag{7}
$$
There is at most one observer in the second alternative. The ordinary separation and t∈Δ hypotheses are part of this assertion.

Now suppose CentreSep(t,Δ), not merely ordinary separation. If identity is the only central observer, central separation gives the Fregean Axiom and hence full Extensionality over C. Otherwise fix the nonidentity central E and its true kernel k. Put a=¬k. Boolean preservation gives Ek=0 and Ea=1. The two central observers I,E give the following current truth profiles:

| Proposition | Its current truth | Truth of its E-image |
| --- | --- | --- |
| 0 | false | false |
| k | true | false |
| a | false | true |
| 1 | true | true |

For any p, its pair of truth values agrees with one row. Since all central observers are I or E, central separation identifies p with that row's proposition. Thus
$$
\forall p\,(p=0\lor p=k\lor p=a\lor p=1).
\tag{8}
$$
The four values are distinct: k is true and Ek=0, while a is false and Ea=1. They form the four-element Boolean algebra. In particular k is the true atom and a the false atom. This proves Actuality: k lies below every true proposition. In the identity-only case the actual world is 1.

For later use define the single finitary cardinal bound
$$
\mathrm{Four}_t:=(\exists u_0u_1u_2u_3\,
 \forall p\,\bigvee_{i=0}^{3}p=u_i).
\tag{9}
$$
Repeated witnesses are allowed. We have proved that full CentreSep over H implies Four_t and Actuality. Four_t also gives internal Frege finiteness of all propositions by four successive adjoining-member steps, omitting repetitions. This is an internal fixed finite proof, not a replacement of arbitrary internal finiteness by an external enumeration. Over C the proposition algebra therefore has either one or two Boolean atoms.

## 3. Native necessity is forced in the nontrivial case

Continue with the four-element case above, and add BF_t, as supplied by full separation. C provides the unconditional identities
$$
(p=q)=\Box(p\leftrightarrow q),
\qquad
(p\ne q)=\Diamond(p\mathbin\triangle q),
\tag{10}
$$
and in particular (p=0)=□¬p. These are C Boolean-modal identities: C proves the corresponding equivalences, and necessitation and Intensionality identify their propositions. No instance of (10) is obtained by necessitating an optional hypothesis.

Modal reflexivity gives □k≤k and □a≤a. Since k is a true proper atom, □k cannot be k: its current truth would say k=1. Hence □k=0. The other value satisfies □a=0 or □a=a.

Suppose □a=0. Then each nonzero proposition d has ◇d=1, by checking d=k,a,1 using □k=□a=0. If p≠q, its symmetric difference is nonzero, so (10) makes the inequality proposition p≠q identical to 1. Therefore ND_t holds.

The exact recorded chain is
$$
\mathrm{ND}_t+\mathrm{BF}_t
\ \Longrightarrow\ \Box\mathrm{ND}_t
\ \Longrightarrow\ \Box\mathrm{ND}_{\text{all relational types}},
\tag{11}
$$
giving C5. The first implication is [the type-t Barcan argument](../../source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml); the second is [the boxed type reduction](../../source/topics/classicism/results/necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r.yaml). They are proved implications, not necessitation of the current ND_t assumption.

But the established C5 central-separation theorem would now give Extensionality, contradicting the four distinct values. Thus
$$
\Box0=0,\quad\Box k=0,\quad\Box a=a,\quad\Box1=1.
\tag{12}
$$
The nonidentity central observer has E0=Ek=0 and Ea=E1=1. Checking these four inputs in (12) gives E(□p)=□Ep for every p. Functionality collects the whole native-Box commutation identity. Identity has that identity as well. The central witnesses are therefore both idempotent and native-Box preserving.

For an arbitrary requested qualification list, use central separation at its enlargement by t. The resulting central witnesses need only be retained as Good, idempotent and Box-preserving observers at the original list. This step does not infer that centrality itself is monotone under removing types from its list.

Consequently, at full schema scope over H,
$$
\boxed{
\mathrm{CentreSep}\ \Longrightarrow\
\mathrm{IdemBoxSep}+\mathrm{Four}_t
 +\mathrm{Actuality}+\mathrm{Fin}_t(\mathrm{All}).}
\tag{13}
$$
It also implies FinBoxSep, because every admitted observer has internally finite image once all propositions are internally finite. The image-induction fact is proved in [Finite-image native-Box observers](finite-image-native-box-observers.md), §2.

## 4. The exact converse over H

**Theorem 1.** At full relational schema scope,
$$
\boxed{
\mathrm H+\mathrm{CentreSep}
\quad\equiv\quad
\mathrm H+\mathrm{IdemBoxSep}+\mathrm{Four}_t.}
\tag{14}
$$
The forward implication is (13). For the reverse implication, full IdemBoxSep supplies C, BF and Functionality. If every proposition is 0 or 1, Extensionality follows and identity supplies full central separation.

Otherwise choose a proper nonzero proposition and take it or its complement to obtain a currently true proper k. Put a=¬k. Four_t implies that the distinct values 0,k,a,1 exhaust the proposition algebra. Thus k and a are atoms, with a currently false.

For any desired finite Δ, choose an idempotent native-Box $\mathrm{Good}_\Delta$ observer B that distinguishes a from 0. Propositional separation at that list supplies it, and Ba must be true. Every Boolean observer on the four-element algebra is determined by its value on k. The four possible values give identity, the atom swap, or one of the two endpoint readers. Identity and the reader of k do not accept a. The swap is not idempotent. Consequently
$$
Bk=0,\qquad Ba=1.
\tag{15}
$$
Since □a≤a, its only possibilities are 0,a. Native-Box commutation gives B(□a)=□Ba=1, excluding □a=0. Thus □a=a. As before □k=0. Using (10),
$$
(k=0)=a,\qquad(a=0)=0.
\tag{16}
$$
Now consider **any admitted Boolean observer G**, without imposing any quantifier qualification. Equality congruence is an unconditional logical law, and therefore gives the algebraic inequality
$$
(k=0)\le(Gk=G0).
\tag{17}
$$
If Gk=1, the right side is (1=0)=0. If Gk=a, it is (a=0)=0. Either case contradicts the nonzero left side a. Hence Gk is 0 or k. Boolean preservation then makes G agree with B or I on all four inputs; Functionality gives G=B or G=I as whole objects.

It follows that B commutes with every $\mathrm{Good}_\Delta$ observer: they are among I and B, and B is idempotent. Thus B is central at the original Δ. This argument excludes the unwanted maps already at the Boolean level; it does not rely on an invalid inference from centrality at a larger list to centrality at a smaller one.

The current profiles of I and B distinguish all four propositions. Available Functionality lifts their separation to any requested relational output type. This establishes the full central schema and proves (14). ∎

The implication CentreSep⇒IdemBoxSep is strict over H. The full four-point diamond has ☐IdemBoxSep but its root proposition algebra has sixteen elements and fails central separation, by the [finite-poset centre classification](central-logical-observers.md), §5. The same diamond has FinBoxSep, so CentreSep⇒FinBoxSep is strict too. Conversely Extensionality⇒CentreSep is strict: the full two-point chain has four propositions and ☐CentreSep but fails Extensionality. The previously established incomparabilities with Rev and End remain intact.

Equation (14) is an intrinsic theory characterization, unlike the earlier classification of one finite model family. Four_t is the displayed exact bound. It is not replaced by arbitrary internal finiteness, by a bound on the observer family, or by a C5 premise.

## 5. Central separation persists

**Theorem 2.** At full schema scope over H,
$$
\boxed{\mathrm{CentreSep}
\quad\longleftrightarrow\quad
\Box\mathrm{CentreSep}.}
\tag{18}
$$
The box means the separate box of each finite-list, relational-output separation formula. There is no infinitary conjunction in the language. The reverse implication is modal reflexivity. We prove the forward implication without necessitating an optional separation hypothesis.

Fix the output type τ and finite list Δ whose central separation formula is to be boxed. The preceding argument supplies admitted propositions k,a and an observer B with the following current properties:
$$
\begin{gathered}
a=\neg k,\qquad
\forall p\,(p=0\lor p=k\lor p=a\lor p=1),\\
(k=0)=a,\qquad(a=0)=0,\\
Bk=0,\qquad Ba=1,\qquad\mathrm{Good}_\Delta(B).
\end{gathered}
\tag{19}
$$
In the four-element case take the nonidentity central observer at a list enlarged by t, then forget the extra Good qualification. Equations (16) follow from (12). In the two-element case take k=0, a=1 and B=I. Thus (19) is available in either case.

**Finite structural lemma.** Over C with the required current Functionality, (19) implies CentreSep(τ,Δ).

To verify the lemma, first suppose k is currently false. Then a is true, so the identity (k=0)=a makes k=0 true. Hence a=1, and the enumeration leaves only the two endpoints. Every Boolean observer is I by Functionality, and identity separates.

If k is true, the identities Bk=0 and Ba=1 exclude k=1 and a=0. The four enumerated values are then distinct. Equations (16)–(17) exclude Gk=1,a for every Boolean G, so all such observers are I or B. In particular B is idempotent, I and B are central for $\mathrm{Good}_\Delta$, and their two current truth profiles distinguish the four values. Functionality gives the asserted relational separation. This proves the lemma without assuming that the truth of k persists.

All individual identities in (19) persist by Necessity of Identity. $\mathrm{Good}_\Delta$(B) is a finite conjunction of whole-operation identities, so it persists for the same reason. For the enumeration, each currently true equality disjunct persists; finite disjunction therefore gives
$$
\forall p\,\Box(p=0\lor p=k\lor p=a\lor p=1).
\tag{20}
$$
BF_t collects (20) into the necessary enumeration. This uses identity persistence and the proved Barcan instance, not necessitation of an optional material universal.

By (13), full CentreSep implies BoxSep. The established [native-Box consequence](native-box-logical-observers.md), §3, gives necessary Functionality at every required type. Thus every premise of the finite structural lemma, including its Functionality instances, is now available necessarily for these parameters.

Discharge the structural lemma's premises and universally close its parameters. It is then an unconditional C theorem for the fixed τ,Δ. Necessitate that theorem, instantiate its parameters by the standard modal quantifier rules, and use the necessary premises just obtained. The conclusion is □CentreSep(τ,Δ). Since the requested output type and finite list were arbitrary, this proves (18). ∎

The persistence statement is stronger than the fact that each individual qualifying witness preserves its qualification. It controls the entire future central class through the persistent finite identities (19). In particular it avoids assuming that current commutation with every qualified observer is automatically necessary commutation with every future qualified observer.

## 6. Sources

- Direct source for the C5-free kernel construction, four-value characterization and persistence argument: `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, this note, §§1–5, unpaginated.
- [Central logical observers](central-logical-observers.md), §§1–5: centrality, Boolean patches, idempotence, the earlier C5 collapse, and the finite rooted-poset centre calculation.
- [Typed separation and Classicism](typed-separation-and-classicism.md), §§3–7: full H logical separation supplies C, BF and Functionality.
- [ND_t with BF_t gives necessary ND_t](../../source/topics/classicism/results/nd-t-and-bf-t-imply-necessary-nd-t.yaml): Bacon and Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.4, p. 23. [Boxed ND_t implies boxed all-type ND](../../source/topics/classicism/results/necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r.yaml): Proposition 2.2, p. 22. These are the exact type steps in (11).
- [Fregean implies full Extensionality](../../source/topics/classicism/results/fregean-axiom-implies-extensionality-r.yaml): Bacon and Dorr, *Classicism*, draft of 16 May 2023, §1.4, p. 16 and note 18.
- [Native-Box logical observers](native-box-logical-observers.md), §3: full BoxSep gives necessary BF and necessary Functionality. [Idempotent native-Box observers](idempotent-native-box-observers.md), §§3–6: the full diamond and two-point-chain model ingredients. [Finite-image native-Box observers](finite-image-native-box-observers.md), §2: internal finite adjoining and image closure.

No database record, central atlas file, published proof or formal-verification status is changed by this note.
