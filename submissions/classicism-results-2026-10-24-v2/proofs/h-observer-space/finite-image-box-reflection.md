# Finite-image native-Box separation reflects global finiteness

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new arguments: `misc`, this note, §§1–5, unpaginated.

Actuality can be removed from the full finite-image native-Box separation theorem. The decisive fact is an internal finiteness reflection lemma for each observer: if its observed image of a predicate is finite, it accepts the proposition that the predicate is finite. This uses native-Box commutation, Boolean preservation, and the universal quantifier at type t. It does not assume that the observer is injective or that an actual world exists.

Consequently one propositional separation instance with qualification list {t} already makes the proposition “all propositions are finite in number” identical to Top, over C. The same conclusion holds when the list contains any relational type: its quantifier law supplies the type-t law by a definable retraction. At full relational schema scope over H, finite-image native-Box separation is exactly native-Box separation together with internal finiteness of the entire proposition domain. The resulting separation schema need not persist, even when the finite-domain condition does.

## 1. Qualification, finiteness and theorem acceptance

Use $`\mathrm{Good}_\Delta`$ and the whole-operation native-Box identity from [Native-Box logical observers](native-box-logical-observers.md):

```math
 \mathrm{BoxComm}(E):\quad
 (\lambda p.E(\Box p))=(\lambda p.\Box Ep),
 \qquad \Box p:=(p=\top)
 \tag{1}
```

Throughout §§1–3, work over C and assume that the finite external list Δ contains at least one relational type σ, meaning σ≠e. In particular Δ={t} suffices. The retraction argument below derives the needed Q_t law from Q_σ; no other qualification type is required. Write FinBoxSep(τ,Δ) for separation at the fixed relational output type τ by the common class $`\mathrm{Good}_\Delta`$∧BoxComm∧FinIm, where

```math
 \mathrm{Im}(E)(q):=\exists p\,(Ep=q),
 \qquad
 \mathrm{FinIm}(E):=\mathrm{Fin}_t(\mathrm{Im}(E))
 \tag{2}
```

BoxSep omits FinIm. These are the same definitions as in [Finite-image native-Box observers](finite-image-native-box-observers.md). That earlier note proves the fixed-instance equivalence with an Actuality premise for **every** finite Δ. The present argument removes Actuality when Δ contains a relational type, without changing the earlier arbitrary-list theorem.

**Retraction of relational quantifiers to t.** Write σ=ρ̄t and fix an argument tuple ā of the indicated types. The admitted constant-relation map c(p)=λx̄.p and evaluation map r(X)=X[ā] satisfy r(c(p))=p by beta conversion. H proves, with ā and F free,

```math
 \forall X^\sigma\,F(r(X))\quad\leftrightarrow\quad
 \forall p^t\,Fp
 \tag{2a}
```

For the forward direction instantiate X with c(p); the reverse direction instantiates p with r(X). C's Logical Equivalence therefore gives identity of the whole lambda-F operations in (2a). If E satisfies the whole Q_σ law, precompose that law with F↦λX.F(r(X)). Using (2a) on both sides gives the whole Q_t law:

```math
 \begin{aligned}
 E(\forall p\,Fp)
 &=E(\forall X\,F(r(X)))\\
 &=\forall X\,E(F(r(X)))\\
 &=\forall p\,E(Fp)
 \end{aligned}
 \tag{2b}
```

This calculation is an identity of the displayed lambda-F operations, obtained by composition and substitution of the supplied whole identities. It does not infer a whole identity from an optional pointwise equivalence. The arbitrary ā parameters can be discharged using the standing nonempty type domains; the resulting law contains none of them. For σ=t the retraction is identity.

Likewise a whole existential-preservation law at any relational σ suffices: C's unconditional whole-operation Boolean duality between the primitive existential and universal quantifiers, together with Boolean preservation by E, converts it to Q_σ, and then (2b) applies. These reductions need neither BF nor Functionality nor Actuality. No such retraction is asserted for the individual type e, since the language does not admit operations with individual-valued output.

For clarity, the internal Frege definitions at type t are

```math
\begin{aligned}
 \mathbf0(U)&:=\forall x\,\neg Ux,\\
 \mathrm{Suc}(Z)(U)&:=\exists x\,
 [Ux\land Z(U\setminus\{x\})],\\
 (U\setminus\{x\})(p)&:=Up\land p\ne x,\\
 \mathrm{FC}(Z)&:=\forall W\,
 [(W\mathbf0\land\forall Y(WY\to W(\mathrm{Suc}(Y))))\to WZ],\\
 \mathrm{Fin}(U)&:=\exists Z\,[\mathrm{FC}(Z)\land ZU]
\end{aligned}
\tag{3}
```

Here U:tt, Z:(tt)t and W:((tt)t)t; Fin abbreviates Fin_t. Types in these definitions do not automatically become observer-qualification requirements. The proof below never moves E through the higher-type quantifiers inside FC or Fin.

We use two unconditional H theorems:

```math
 \mathbf0(U)\to\mathrm{Fin}(U),
 \qquad
 [Ux\land\mathrm{Fin}(U\setminus\{x\})]
       \to\mathrm{Fin}(U)
 \tag{4}
```

The first uses cardinality witness 0. For the second, if Z witnesses finiteness of the deletion, Suc(Z) witnesses finiteness of U, using x. FC(0) and FC(Z)→FC(Suc(Z)) follow directly from (3). Thus (4) requires neither a finite enumeration nor an extensionality principle.

An unconditional H theorem T, including one with the displayed free parameters, is H-equivalent to Top. C's Logical Equivalence identifies its appropriate lambda abstraction with the constant-Top abstraction; application gives T=Top. Hence every Boolean observer accepts that theorem instance: ET=E Top=Top. Boolean preservation then converts (4) into the usable current implications

```math
 E(\mathbf0(U))\to E(\mathrm{Fin}(U)),
 \qquad
 [E(Ux)\land E(\mathrm{Fin}(U\setminus\{x\}))]
       \to E(\mathrm{Fin}(U))
 \tag{5}
```

Only the unconditional formulas in (4) receive this treatment. Neither Fin(U), nor the qualification of E, nor an induction hypothesis is assumed to be a theorem or is necessitated.

Native-Box commutation supplies a second crucial identity. The unconditional C Boolean-modal identity (p=x)=□(p↔x), together with Boolean preservation, gives

```math
 \boxed{E(p=x)=(Ep=Ex)}
 \tag{6}
```

Indeed E□(p↔x)=□E(p↔x)=□(Ep↔Ex). This is commutation with proposition identity judgments, derived here from native Box; no extra equality qualification is imposed.

## 2. Internal reflection from the observed image

Fix such an admitted observer E. For an admitted V:tt define

```math
 I_E(V)(q):=\exists p\,[Ep=q\land E(Vp)]
 \tag{7}
```

This is an admitted predicate. Its members are the E-images of inputs whose V-membership E currently accepts. In particular it is not generally the image of the current extension of V.

**Lemma.** If I_E(V) is internally finite, then E(Fin(V)) is currently true:

```math
 \boxed{\mathrm{Fin}(I_E(V))\to E(\mathrm{Fin}(V))}
 \tag{8}
```

The proof is Frege induction. Let Ext(Z) say that Z is invariant under current coextension of predicates:

```math
 \mathrm{Ext}(Z):=\forall U,V\,
 [\forall p(Up\leftrightarrow Vp)\to(ZU\leftrightarrow ZV)]
 \tag{9}
```

and use the single admitted induction predicate

```math
 W_E(Z):=\mathrm{FC}(Z)\land\mathrm{Ext}(Z)
 \land\forall V\,[Z(I_E(V))\to E(\mathrm{Fin}(V))]
 \tag{10}
```

The bookkeeping conjuncts FC and Ext are deliberate. Ext holds at zero and passes to a successor: the same deletion witness works for coextensive predicates, and the deleted predicates are still coextensive. Thus it is available at the predecessor used below, without treating coextension as identity. FC also holds at zero and passes to successors by (3).

**Zero.** Suppose 0(I_E(V)). Every E(Vp) is false: otherwise q=Ep would belong to I_E(V). The whole type-t universal law and Boolean preservation give

```math
 E(\mathbf0(V))
 =E(\forall p\,\neg Vp)
 =\forall p\,\neg E(Vp)
 \tag{11}
```

The right side is true. The first implication in (5) therefore gives E(Fin(V)). This proves W_E(0).

**Successor.** Assume W_E(Z) and Suc(Z)(I_E(V)). Choose y such that

```math
 I_E(V)(y),\qquad Z(I_E(V)\setminus\{y\})
 \tag{12}
```

Choose x witnessing the first conjunct, so Ex=y and E(Vx) is true. Put V′:=V\setminus\{x\}. Equation (6) gives, at every p,

```math
 E(V'p)=E(Vp)\land(Ep\ne Ex)
 \tag{13}
```

It follows by ordinary quantified reasoning that

```math
 \forall q\,[I_E(V')(q)\leftrightarrow
             (I_E(V)(q)\land q\ne y)]
 \tag{14}
```

This is the important deletion step. Deleting x from V deletes the **entire observed fibre** Ex=y from I_E(V), because the equality test inside the observed membership is also transformed by E. No injectivity assumption is used.

Ext(Z), (12) and (14) give Z(I_E(V′)). The induction hypothesis gives E(Fin(V′)). Together with E(Vx), the second implication in (5) now gives E(Fin(V)). The FC and Ext bookkeeping clauses also pass to Suc(Z), completing the induction step.

Given a witness Z for Fin(I_E(V)), its defining FC instance at W_E yields W_E(Z), and its membership Z(I_E(V)) gives the conclusion of (8). This completes the internal proof.

The only quantifier preservation law used inside an E-expression in the induction was Q_t in (11), either supplied directly or derived by (2b). The ordinary induction predicate (10) quantifies over higher types, but its admission does not require E to commute with those quantifiers. Witnesses x,y,Z are chosen within individual existential-elimination steps; no choice function or external standard-cardinality assumption is introduced.

## 3. Separation makes global finiteness necessary

Put All:=λp.Top and FinAll:=Fin(All). Since E Top=Top, I_E(All) is currently coextensive with Im(E). Fin is invariant under current coextension by the same zero/successor induction used in (9); see also the earlier finite-image note, §2. Thus (8) implies

```math
 \mathrm{Good}_\Delta(E)\land\mathrm{BoxComm}(E)
 \land\mathrm{FinIm}(E)
 \quad\Longrightarrow\quad E(\mathrm{FinAll})
 \tag{15}
```

Every member of this qualifying class also accepts Top. Propositional FinBoxSep(t,Δ) therefore identifies FinAll with Top:

```math
 \boxed{\mathrm C+\mathrm{FinBoxSep}(t,\Delta)
       \ \vdash\ \mathrm{FinAll}=\top
       \quad(\sigma\in\Delta,\ \sigma\ne e)}
 \tag{16}
```

In particular it proves both FinAll and □FinAll. This conclusion is an application of separation to the two propositions FinAll and Top; it does not assume that current separation persists.

At any fixed relational output type τ, FinBoxSep(τ,Δ) supplies the same propositional instance. Apply it to the constant τ-relations with values p and q; observer agreement on p,q gives agreement at every argument tuple, and equality of the constant relations gives p=q by application. The standing nonempty type domains supply an argument tuple. No Functionality premise is needed for this reduction.

The converse direction uses the internal finite-image lemma: every admitted image of an internally finite predicate is internally finite, by zero/successor induction and adjoining one output at a time. Hence FinAll makes every admitted E finite-image. The classes qualifying BoxSep and FinBoxSep are then identical.

We have proved the exact local theorem, for every fixed relational τ and every finite Δ containing a relational type:

```math
 \boxed{
 \mathrm{FinBoxSep}(\tau,\Delta)
 \quad\longleftrightarrow\quad
 \mathrm{FinAll}\land\mathrm{BoxSep}(\tau,\Delta)
 \qquad\text{over C}}
 \tag{17}
```

The forward direction additionally gives □FinAll. No Actuality, C5, BF, Functionality, Choice or Boolean Completeness is assumed in this local theorem. The old theorem with Actuality remains available for arbitrary Δ. Whether Actuality can also be removed when Δ is empty or contains only e is unresolved here; no typed countermodel or converse is asserted for those remaining cases.

## 4. Full schemas over H and the C5 region

At full schema scope, FinBoxSep implies ordinary full OS and therefore recovers C, BF and Functionality by [Typed separation and Classicism](typed-separation-and-classicism.md). Apply (16) at the single list {t}. Conversely, full BoxSep recovers C, and FinAll makes every image finite. Therefore

```math
 \boxed{
 \mathrm H+\mathrm{FinBoxSep}
 \quad\equiv\quad
 \mathrm H+\mathrm{FinAll}+\mathrm{BoxSep}}
 \tag{18}
```

These are full theories over relational output types and finite external lists. A single propositional instance over bare H is not being used to recover C. The forward theory also proves Actuality: under FinAll the nonempty meet-closed predicate of true propositions has a least member by the internal finite-fold argument in [Finite semilattice normalization](finite-semilattice-normalization.md), §2. It proves □FinAll by (16).

Thus Actuality is a consequence of full FinBoxSep rather than a necessary added premise. Requiring each individual native-Box witness to have an internally finite image already forces internal finiteness of the entire proposition domain. This remains different from imposing a fixed external bound on the image or requiring one finite family of witnesses.

In the C5 region the result combines with the established inverse and endpoint theorems:

```math
 \boxed{
 \mathrm{C5}+\mathrm{FinBoxSep}
 \quad\equiv\quad
 \mathrm H+\mathrm{Rev}+\mathrm{FinBoxSep}
 \quad\equiv\quad
 \mathrm H+\mathrm{End}+\mathrm{FinAll}}
 \tag{19}
```

Here End and Rev are the full endpoint and reversible logical separation schemas. To check the forward implication, (18) gives FinAll and BoxSep. Under C5, a Good observer commutes with native Box exactly when it is currently injective. Internal finiteness makes an admitted injective operation onto, by the internal finite-domain argument in [One-sided inverse separation on the fork](fork-one-sided-inverse-separation.md), §5. The C5 qualified-section construction then gives an admitted qualified right inverse; injectivity makes it a two-sided inverse. Enlarging a requested finite list by t provides exactly the qualification needed for that construction. Thus the Box witnesses give full Rev.

Under FinAll, all Good observers have finite images, so ordinary finite-image logical separation also follows from OS. The established Rev plus finite-image separation theorem gives End. Conversely End gives Rev and C5; reversibility gives Box commutation under C5, and FinAll makes every witness finite-image. This proves (19).

The FinAll conjunct on the final side is substantive. The older equivalence Rev plus ordinary finite-image separation with End does not force the whole proposition domain to be finite. It is the additional native-Box restriction in FinBoxSep that does so here.

## 5. Comparisons using existing models

The following consequences use only already-audited full action models.

- FinBoxSep strictly implies BoxSep. The full infinite omega chain has BoxSep, while its full proposition domain is not internally finite. It therefore fails FinBoxSep by (18).
- FinBoxSep and IdemBoxSep are incomparable. The omega chain has join readers and therefore IdemBoxSep but fails FinBoxSep. The finite six-point P_{2,2} model has BoxSep and FinAll, hence FinBoxSep, but fails IdemBoxSep.
- FinBoxSep is incomparable with Rev and with End. The full two-point chain has FinBoxSep and fails C5, hence fails both Rev and End. A full infinite S5 cluster has End and Rev but fails FinAll, hence fails FinBoxSep.
- FinBoxSep does not imply its separately boxed schema, even with □FinAll. The ten-point exterior-arm model $`A_{2,3}`$ has BoxSep at its root and finite proposition domains at every point. Hence it has full FinBoxSep and □FinAll. Its future cone P_{2,3} fails BoxSep(t,{t}), and therefore fails FinBoxSep(t,{t}).

The omega model is in [Omega-chain surjective observers](omega-chain-surjective-observers.md); its idempotent join readers and the finite P_{2,2} and two-point-chain models are in [Idempotent native-Box observers](idempotent-native-box-observers.md), §§3–6. The internal/external finiteness comparison for full domains is the standard-numeral-predicate argument in the earlier [finite-image note](finite-image-native-box-observers.md), §5. The S5 endpoint model is the standard full possible-worlds instance of the action construction, with one endpoint evaluation observer for every world. The [exterior-arm model](exterior-arm-posets-native-box-nonpersistence.md), §§2–4, retains C+□BF+□Functionality+□OS+□Atomicity_t+□.2. Its failed future instance is explicit, so the FinBox nonpersistence conclusion needs no new model construction.

More generally, on any full finite rooted-poset model, all admitted observers have internally finite images at every point. Therefore FinBoxSep and BoxSep coincide there point by point, and their separately boxed schemas coincide too. In the $`A_{m,n}`$ family, FinBoxSep always holds at the root, while □FinBoxSep holds exactly when m=1 or n≤m, by the established BoxSep cone table. These are exact evaluations in the stated model family, not a general logical identification of the two schemas.

These comparisons concern the indicated full schemas. They neither assert that FinBoxSep implies C5 nor convert the local theorem (17) into an arbitrary-list result without its relational-qualification hypothesis.

## 6. Sources

The observed-image reflection lemma, the t-only qualification argument, (16)–(19), and the resulting comparisons are original ordinary arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated.

The fixed Frege definitions are in the [background](../../source/topics/classicism/background.md) and [Axiom of Infinity at t](../../source/topics/classicism/principles/axiom-of-infinity-t.yaml). The earlier [finite-image native-Box note](finite-image-native-box-observers.md), §§2–4, supplies the internal coextension, image and preimage inductions and the arbitrary-list Actuality theorem. The new lemma in §2 supplies the additional argument removing Actuality at the stated scope.

The C framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.3 and 1.5, summarized in the [topic framework](../../source/topics/classicism/topic.yaml) and background. The necessary-identity/modal identities and native-Box qualification are used as in [Native-Box logical observers](native-box-logical-observers.md), §§1–4. The qualified inverse is the original construction in [Surjective logical observers](surjective-logical-observers.md), §§2–4. The endpoint/reversible/finite-image theorem is in [Logical observer hierarchy](../logical-observer-hierarchy.md).

The full action-model framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). New comparisons above use the already specified models, without adding database verdicts or changing their certificates.

No central atlas, published proof, database record, named human review or formal-verification status is changed by this note.
