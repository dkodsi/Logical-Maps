# Logical Observer Separation

[Main results](../MAIN-RESULTS.md#logical-observers) · [Proposed principle](../CANDIDATES_DK.md#logical-observer-separation-r) · [Certificate scope](../evidence/RESULT-INDEX.md#logical-observers)

## 1. The principle

An observer is an admitted operation $E^{tt}$. For a finite set $\Delta$ of types, $\operatorname{Good}_{\Delta}(E)$ requires the Boolean operation identities

$$
\begin{aligned}
E\top&=\top,&E\bot&=\bot,\\
(\lambda p\, .\,E(\neg p))&=(\lambda p\, .\,\neg Ep),\\
(\lambda p,q\, .\,E(p\land q))&=(\lambda p,q\, .\,Ep\land Eq),\\
(\lambda p,q\, .\,E(p\lor q))&=(\lambda p,q\, .\,Ep\lor Eq).
\end{aligned}
$$

For each $\sigma\in\Delta$, it also requires the quantifier operation identities

$$
\begin{aligned}
(\lambda F^{\sigma t}\, .\,E(\forall x^\sigma\, .\,Fx))&=(\lambda F^{\sigma t}\, .\,\forall x^\sigma\, .\,E(Fx)),\\
(\lambda F^{\sigma t}\, .\,E(\exists x^\sigma\, .\,Fx))&=(\lambda F^{\sigma t}\, .\,\exists x^\sigma\, .\,E(Fx)),
\end{aligned}
$$

and the equality laws

$$
\begin{aligned}
&\forall x^\sigma\, .\,E(x=x),\\
&\forall x,y^\sigma\, .\,\forall F^{\sigma t}\, .\,E(x=y)\to(E(Fx)\to E(Fy)).
\end{aligned}
$$

Logical Observer Separation is the schema

$$
\forall X,Y^{\bar\sigma t}\, .\,X=Y\leftrightarrow\forall E^{tt}\, .\,\operatorname{Good}_{\Delta}(E)\to\forall\bar z^{\bar\sigma}\, .\,\bigl(E(X[\bar z])\leftrightarrow E(Y[\bar z])\bigr).
$$

The tuple $\bar\sigma$ can be empty. Each $\Delta$ is finite; types index the schema rather than being quantified in its language. The identity observer qualifies in H by conversion and the H equality axioms.

## 2. Why the equality laws occur

The clauses say that the observer's interpretation validates reflexivity and substitution. They are used when transporting proofs of H, whose logical vocabulary includes equality. They do not require $E(x=y)=(x=y)$.

**Over C, both equality clauses follow from Boolean preservation alone.** H proves reflexivity and the substitution formula $(x=y)\to(Fx\to Fy)$. Logical Equivalence in C gives

$$
(x=x)=\top,\qquad\bigl((x=y)\to(Fx\to Fy)\bigr)=\top.
$$

Apply $E$ to these identities. Its top law proves the reflexivity clause; its Boolean laws turn the second identity into the substitution clause. Generalize the displayed variables. No quantifier-preservation premise or enlargement of $\Delta$ is needed.

The equality laws are therefore a natural requirement for the formulation over H, and redundant once C is assumed. The proof below uses them over H; it does not establish that every clause is indispensable to every possible formulation over H.

## 3. OS entails C and BF over H

**Theorem.** $\mathrm H+\mathrm{OS}\vdash\mathrm C+\mathrm{BF}$ at every type.

For each H proof of $P$, there is a finite $\Delta$ such that H proves $\operatorname{Good}_{\Delta}(E)\to EP$, with $E$ fresh. Include the types of all quantifier and equality steps. Induct on the proof: Boolean preservation supplies propositional reasoning and modus ponens; application of the quantifier operation identities supplies instantiation, existential introduction and generalization; the equality laws supply reflexivity and substitution. For a conversion equation $A=B$, begin with $E(A=A)$ and substitute using the H equation inside $\lambda u\, .\,E(A=u)$. Substitution and renaming commute with this construction because $E$ is fresh.

If H proves $P\leftrightarrow Q$, all qualified observers agree on $P,Q$. Apply separation to the instances of $\lambda\bar z\, .\,P$ and $\lambda\bar z\, .\,Q$ at their relational type. Conversion gives

$$
(\lambda\bar z\, .\,P)=(\lambda\bar z\, .\,Q).
$$

This is Logical Equivalence, hence C. The conclusion identifies the abstractions themselves.

For BF at $\sigma$, suppose $\forall x^\sigma\, .\,Fx=\top$. Every observer qualified at $\sigma$ then has $E(Fx)=\top$ for each $x$. Universal preservation makes $E(\forall x\, .\,Fx)$ true, so it agrees in truth with $E\top$. Proposition separation gives $(\forall x\, .\,Fx)=\top$, the desired necessary universal proposition. Generalize $F$. No optional assumption was necessitated.

## 4. A simpler formulation over C

Let $S_\Delta$ be separation at type $t$ using just the Boolean and quantifier operation identities in §1. Over C,

$$
\mathrm{OS}\quad\longleftrightarrow\quad\{S_\Delta:\Delta\text{ finite}\}.
$$

By §2 the observer classes are identical. OS gives each $S_\Delta$. Conversely, the proposition separation schemas give BF by §3. If all qualified observers agree on every instance of $X,Y$, $S_\Delta$ makes those instances identical. C + BF gives Functionality: NI makes each identity necessary, BF brings these necessities under universal quantification, and modalized Functionality identifies the operations. Iterate through the argument tuple to obtain $X=Y$.

Thus, as theories over H, OS is equivalent to C plus this propositional separation schema. The equality clauses can be omitted when stating it against the database's fixed background C.

## 5. Atomicity supplies observers under ☐BF

**Theorem.** Over C,

$$
\operatorname{Atomicity}(t)+\Box\mathrm{BF}\ \vdash\ \mathrm{OS}.
$$

For an atom $a$, put $c=\Diamond a$ and

$$
O_a(p):=(c\land\Box(a\to p))\lor(\neg c\land p).
$$

The Boolean calculation needs no stability assumption on $a$. An atom lies below either $p$ or $\neg p$. In the first case the outputs at $p,\neg p$ become $c\lor p$ and $\neg c\land\neg p$; the second case reverses these. Hence negation is preserved. Meet and the endpoint laws follow from distribution and unconditional C modal identities; join follows by De Morgan. NI and BF at $t$ collect the output identities under their proposition arguments, and Intensionality gives the Boolean composite identities.

C proves the following unconditional theorem, without assuming atomhood:

$$
\mathrm{BF}_\sigma\to\forall a,F\, .\,\bigl(O_a(\forall x^\sigma\, .\,Fx)\leftrightarrow\forall x^\sigma\, .\,O_a(Fx)\bigr).
$$

When $c$ is true, BF and CBF give the equivalence for $\Box(a\to p)$. When $c$ is false, $a=\bot$ and $O_a$ is the identity. Necessitate this theorem, then apply $\Box\mathrm{BF}_\sigma$, K and CBF. The resulting necessary universal equivalence gives the quantifier composite identity by Intensionality. Boolean preservation and quantifier duality give the existential identity.

If $p\ne q$, choose an atom below their Boolean symmetric difference. Its $O_a$ distinguishes them in truth, proving every $S_\Delta$. Section 4 yields OS. More precisely, the sufficient premise for $S_\Delta$ is Atomicity at $t$, BF at $t$, and $\Box\mathrm{BF}_\sigma$ for each $\sigma\in\Delta$; see [operator representation](operator-representation.md).

## 6. The exact case with C5 and Actuality

Over C5 + Actuality,

$$
\mathrm{OS}\quad\longleftrightarrow\quad\operatorname{Atomicity}(t)\quad\longleftrightarrow\quad\Box\mathrm{OS}.
$$

Here $\Box\mathrm{OS}$ consists of the separately boxed instances.

For the forward direction, Actuality supplies a true world $w$. ND at $t$, supplied by C5, makes $w$ necessarily nonbottom. Hence $B(p):=\Box(w\to p)$ is $\top$ when $p$ is true and $\bot$ when $p$ is false. Given nonbottom $d$, separation provides $E$ qualified at $t$ with $Ed$ true. Define $F(p):=B(Ep)$. This preserves Boolean operations, takes endpoint values at current inputs, and agrees with $E$ in truth. The universal law of $E$ therefore gives truth agreement between $F(\forall p\, .\,Xp)$ and $\forall p\, .\,F(Xp)$.

Set

$$
a_F:=\forall p^t\, .\,Fp\to p.
$$

Then $F a_F$ is true: its quantifier calculation reduces to $\forall p\, .\,F(Fp)\to Fp$, and $F(Fp)=Fp$ because $Fp$ is an endpoint. Thus $a_F\ne\bot$. Necessary universal instantiation gives $a_F\le(Fp\to p)$. If $Fp=\top$, this yields $a_F\le p$; otherwise negation preservation gives $a_F\le\neg p$. The nonbottom $a_F$ decides every proposition, so it is an atom. Since $Fd=\top$, it lies below $d$.

Conversely, C5 supplies $\Box$BF and, with Atomicity at $t$, necessary Atomicity at $t$. Apply the necessitated theorem of §5, using axiom 4 on the boxed BF premises. This gives every instance of $\Box$OS; T gives OS. Actuality is needed only for the converse to Atomicity.

## 7. Bounds and countermodels

Over C, the sufficient condition of §5 is strictly stronger than OS, while OS is strictly stronger than BF.

The finite-support permutation model satisfies the composite identities and separates propositions. A finite-support permutation can agree on a finite pinning set with an arrow distinguishing two propositions. Its transport operator is admitted; inverse image preserves Boolean operations and both quantifiers at every future input, using bijectivity of transport on each typed domain. Sections 2 and 4 supply the equality laws and separation at all relational types. The model is atomless and fails Actuality and Extensionality. The detailed admission argument is in [permutation observers](observer-models.md).

The qualitative-contrast model at $W_0$ satisfies C5 + Actuality + $\Box$BF and fails Atomicity at $t$. By §6 it fails OS. Thus this stronger Barcan background still does not supply OS. The [countermodel proof](observer-countermodel.md) also establishes a direct Boolean obstruction.

The full-surjection-monoid model satisfies Atomicity at $t$ and $\Box$BF, so §5 gives OS. It fails ND at $t$. Thus OS does not imply ND and is not C5.

At $W_1$ of the qualitative-contrast construction the composite observers do separate; $W_0$ is accessible and fails separation. Thus OS does not imply $\Box$OS; see [the two evaluation points](local-observers.md).

Atomicity at $t$ plus BF suffices for OS by the [guarded atomic construction](observer-lattice.md#5-atomicity-improves-the-logical-separation-upper-bound). Whether OS entails $\Box$BF remains unsettled.

## 8. Necessary OS and possible Actuality

Over C5,

$$
\Box\mathrm{OS}\ \vdash\ \bigl(\Diamond\mathrm{Actuality}\to\Box\mathrm{Plenitude}\bigr).
$$

The conclusion is read instancewise for the Plenitude schema. Fix a target instance. The proof in §6 and the recorded C5 + Atomicity implication give a finite derivation of that boxed Plenitude instance from C5 + OS + Actuality. C5 persists by axiom 4; the needed OS instances hold necessarily by hypothesis. Necessitating the discharged finite derivation therefore shows that possible Actuality implies the possibility of the boxed target. C5 supplies axiom 5, so $\Diamond\Box P\to\Box P$ gives the target at the starting point. This argument applies to every Plenitude instance.

In particular, necessary OS gives

$$
\Diamond\mathrm{Actuality}\to\Box\mathrm{Actuality}
$$

over C5. Thus Actuality is either necessary or impossible.

This consequence fails for OS in place of necessary OS. At $W_1$ of the [qualitative-contrast construction](local-observers.md), C5 and OS hold, while Actuality fails. An arrow to $W_0$, where Actuality holds, makes Actuality possible at $W_1$. Plenitude fails there because it implies Actuality. This is a separation by a named structural consequence, in addition to the failure of necessary OS itself.

Necessary OS also entails necessary BF, by necessitating the finite implication proofs in §3. Whether OS alone already entails necessary BF remains unsettled here.

## 9. Endpoint and factive observers

The [observer hierarchy](logical-observer-hierarchy.md) proves that full typed endpoint separation is exactly C5 + Atomicity (type t) over H, without Actuality. Endpoint observers return only $\top$ or $\bot$. Factive separation is exactly Extensionality, type by type over H. Under Extensionality, truth is endpoint-valued and the identity observer separates all propositions. Given OS, uniqueness of the qualified logical observer is equivalent to Extensionality. Over C, the hierarchy is strict at every arrow:

$$
\small\text{Extensionality}\ \Rightarrow\ \mathrm{C5}+\mathrm{Atomicity}_t\ \Rightarrow\ \Box\mathrm{OS}\ \Rightarrow\ \mathrm{OS}\ \Rightarrow\ \mathrm{BF}.
$$

Over C, propositional endpoint separation testing quantifiers at $t$ already suffices; one propositional factive-separation instance gives full Extensionality. Requiring $\operatorname{Good}_\Delta(E)$ necessarily leaves qualification unchanged over C, whereas ☐OS is strictly stronger than OS. The linked proof gives the diagonal atom construction and all four countermodels.

## Sources

The observer deductions are ordinary mathematical arguments by Codex, prompted by Daniel Kodsi (23–24 October 2026), source `misc`, unpaginated. Sections 2 and 4 give the simpler equality-law derivation and corresponding reformulation. The other arguments combine the H proof transformation, patched-atom calculation, and [full composite representation theorem](operator-representation.md).

For background logic and models: Bacon–Dorr, *Classicism*, §1.3; in the database's 16 May 2023 draft, Proposition 2.3, pp. 22–23; Proposition 2.6, pp. 25–26; Appendix D, pp. 74–79; and the full-surjection construction, §3.5, pp. 59–61. The observer deductions are not attributed to those authors. Current certification scope is stated separately in the [evidence index](../evidence/RESULT-INDEX.md#logical-observers).

## H structure and quantifier reduction

Over H, full relational separation by any qualification is exactly propositional separation plus Functionality; the [H observer map](h-observer-space/MAP.md) develops the primitive, representation and restriction branches. Over C5, propositional separation by Boolean observers preserving the universal quantifier at $t$ is equivalent to full OS. Over C, the existence of an endpoint-fixing operator with range $\{\top,\bot\}$ is equivalent to modal .2; the [reduction proof](modal-selectors-and-quantifier-reduction.md) uses this to identify the mixed quantifier branches.

**Lean certified:** H + OS ⇒ C + BF with explicit endpoint identities. [Certificate scope and evidence](../evidence/RESULT-INDEX.md#logical-observers).
