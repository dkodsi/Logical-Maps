# Native-Box logical observers: necessary Barcan and injectivity

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new theorems and model verdicts: `misc`, this note, §§1–7, unpaginated. The existing model constructions and description argument are attributed in §8.

Requiring separating logical observers to commute with the original modality strengthens ordinary separation in a different direction from requiring injectivity or a qualified left inverse. It forces necessary Barcan, necessary Functionality and the modal axiom .2, but forces neither C5 nor necessary ordinary separation. Over C5, however, native-Box preservation and current injectivity are exactly the same observer restriction.

## 1. Definitions and scope

Use the revised whole-operation qualification Good_Δ from [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §1. It includes the three primitive Boolean operations, full universal and existential operation identities at the finite external type list Δ, and the translated equality clauses. The latter are redundant over C. Separate endpoint-fixing clauses are unnecessary; over C every Good observer fixes both endpoints.

The **native modality** is the framework's original operation

```math
\Box p:=(p=\top).
```

For an admitted E:tt define

```math
\begin{aligned}
\mathrm{BoxComm}(E)&:\quad
 (\lambda p^t.\,E(\Box p))=(\lambda p^t.\,\Box(Ep)),\\
\mathrm{Inj}(E)&:\quad
 \forall p,q^t\,[Ep=Eq\to p=q].
\end{aligned}
\tag{1}
```

The first condition is an identity of entire operations. It is not a material equivalence or a statement about the auxiliary image modality associated with E.

Write BoxSep(τ,Δ) for the usual separation sentence S_{τ,Δ}[BoxComm], and InjSep(τ,Δ) for S_{τ,Δ}[Inj]. Thus, for τ=σ₁⋯σₙt, BoxSep asserts

```math
\forall X,Y^\tau\left[X=Y\leftrightarrow
 \forall E^{tt}\left(
 \mathrm{Good}_\Delta(E)\land\mathrm{BoxComm}(E)
 \to\forall\bar z\,[E(X[\bar z])\leftrightarrow E(Y[\bar z])]
 \right)\right].
\tag{2}
```

The empty tuple gives τ=t. BoxSep and InjSep without indices denote their full schemas over relational output types and finite Δ. A boxed schema means the separate boxes of its closed instances. SplitMono retains its established meaning: separation by Good E having an admitted Good F, qualified for the same list, with the whole identity F∘E=I.

Forgetting restrictions gives, over H,

```math
\mathrm{SplitMono}\Longrightarrow\mathrm{InjSep}
\Longrightarrow\mathrm{OS},
\qquad
\mathrm{BoxSep}\Longrightarrow\mathrm{OS}.
\tag{3}
```

Each full theory therefore recovers C, current BF and Functionality by [typed H-proof transport](typed-separation-and-classicism.md), §§2–3. Nothing here recovers C from one propositional instance alone.

## 2. Native-Box separation makes Barcan necessary

There is a finite local theorem. For every admitted type σ, over C,

```math
\mathrm{BF}_\sigma+\mathrm{BoxSep}(t,\Delta)
\quad\Longrightarrow\quad\Box\mathrm{BF}_\sigma,
\qquad \{\sigma,\sigma t\}\subseteq\Delta.
\tag{4}
```

Here BF_σ denotes its closed predicate formulation

```math
B_\sigma:=\forall F^{\sigma t}
 \left[(\forall x^\sigma\,\Box Fx)
       \to\Box(\forall x^\sigma Fx)\right].
\tag{5}
```

Assume current B_σ and fix an arbitrary Good_Δ observer E satisfying BoxComm. Its full universal laws at σt and σ, Boolean laws, and native-Box law rewrite E(B_σ) to the proposition

```math
\forall F^{\sigma t}
 \left[(\forall x^\sigma\,\Box E(Fx))
       \to\Box(\forall x^\sigma E(Fx))\right].
\tag{6}
```

For each current F, apply current B_σ to the admitted predicate λx.E(Fx). Thus (6), and hence E(B_σ), is true. Also ETop is true. Since E was arbitrary in exactly the qualifying class of (2), propositional separation gives B_σ=Top. This is □B_σ, proving (4).

The only quantified types used in this transport are σ and σt. No quantified type variable, infinite conjunction, persistence of a separating family, or necessitation of the optional BF premise occurs. In particular, the argument does not assume that BoxSep itself holds necessarily.

Full BoxSep first recovers current BF by (3), and provides every finite list needed in (4). Therefore

```math
\boxed{\mathrm H+\mathrm{BoxSep}
\ \Longrightarrow\ \mathrm C+\mathrm{OS}
 +\Box\mathrm{BF}+\Box\mathrm{Functionality}+.2.}
\tag{7}
```

The necessary-Functionality conclusion uses the recorded [necessary-BF to necessary-Functionality theorem](../../source/topics/classicism/results/necessary-barcan-r-implies-necessary-functionality-r.yaml). For each target instance, its proof necessitates a discharged C theorem with finitely many BF premises, then uses the corresponding boxed premises. It does not box an unclosed schema.

### A propositional consequence requiring no Boolean or quantifier laws

The .2 conclusion has a smaller local premise. Put FixBottom(E):=(EBottom=Bottom). Over C,

```math
\mathrm{Sep}_t[\mathrm{FixBottom}\land\mathrm{BoxComm}]
\quad\Longrightarrow\quad
\forall p^t\,[\Diamond\Box p\to\Box\Diamond p].
\tag{7a}
```

No Good qualification is assumed in the premise of (7a). Suppose ◇□p, that is, □p≠Bottom. Separation supplies a qualifying E that distinguishes □p from Bottom in truth. Since EBottom=Bottom, E(□p) must be true. BoxComm gives □Ep, or Ep=Top.

NI makes both Ep=Top and EBottom=Bottom necessary. The unconditional C theorem

```math
(Ep=\top\land E\bot=\bot)\to p\ne\bot
```

can be necessitated and instantiated with E,p by CBF. Applying it to the two necessary identities yields □(p≠Bottom), which is □◇p. This proves (7a), including its universal closure over p. No optional hypothesis is necessitated.

Over C every Good observer fixes Bottom, so each individual BoxSep(t,Δ), for any fixed finite Δ including the empty list, implies the premise of (7a) by enlarging the separating class. This proves the .2 component of (7) without using BF or either quantifier law. The positive statement remains over C locally; full BoxSep over H supplies C by the separate transport argument.

## 3. Over C5, native-Box preservation is injectivity

For any Good_Δ observer E, C5 proves

```math
\boxed{\mathrm{BoxComm}(E)
\ \leftrightarrow\ \mathrm{Inj}(E).}
\tag{8}
```

C5 makes each identity proposition an endpoint. In particular □p equals Top when p=Top and equals Bottom otherwise. Because E fixes endpoints,

```math
E(\Box p)=\Box p.
\tag{9}
```

If E is injective, then Ep=Top iff p=Top, using ETop=Top. Both □Ep and □p are endpoints with the same truth value, so they are identical. Together with (9) this proves the pointwise native-Box identity. C5 supplies Functionality, collecting it into the whole identity in (1).

Conversely, BoxComm and (9) give □Ep=□p, so E reflects Top. A Boolean homomorphism reflecting Top is injective: if Ep=Eq, then E(p↔q)=Top; reflection gives p↔q=Top, and C's propositional Intensionality gives p=q. This proves (8).

Consequently, at every fixed τ and finite Δ over C5,

```math
\mathrm{BoxSep}(\tau,\Delta)
\ \leftrightarrow\ \mathrm{InjSep}(\tau,\Delta).
\tag{10}
```

No quantifier type has to be added to Δ for this equivalence. The C5 premise remains explicit. In particular, (10) does not identify either restriction with qualified left invertibility.

## 4. Necessary injectivity is exactly an unqualified left inverse

For an arbitrary admitted E:tt, without any preservation assumption, C proves

```math
\boxed{
\Box\mathrm{Inj}(E)
\ \leftrightarrow\
\exists F^{tt}\,[F\circ E=I].}
\tag{11}
```

The box closes the displayed p,q variables in Inj and leaves E as a parameter. The existential inverse in (11) is admitted but is not required to be Good.

Define the admitted description term

```math
D_E(q):=\forall p^t\,[(Ep=q)\to p].
\tag{12}
```

H proves the unconditional implication

```math
\mathrm{Inj}(E)
\to\forall x^t\,[D_E(Ex)\leftrightarrow x].
\tag{13}
```

Indeed, if x is true and Ep=Ex, injectivity gives p=x and hence p; this proves D_E(Ex). Conversely, instantiate the defining universal at p=x and use reflexivity to infer x. Discharge injectivity and universally close E. Necessitate this C theorem, then instantiate E using CBF. From □Inj(E) obtain the necessary universal coextension of D_E∘E and I. C's Intensionality gives their whole-operation identity. This proves the forward implication of (11) without BF, Choice, or an assumption that arbitrary external inverse functions are admitted.

Conversely, suppose admitted F satisfies F∘E=I. NI makes this whole identity necessary. The universally closed implication from that identity to Inj(E) is a C theorem, which can be necessitated and instantiated by CBF. Normality yields □Inj(E). This proves (11).

The description is the same proposition-output device used in the [modalized-Plenitude proof](../../source/topics/classicism/results/classicism-implies-modalized-plenitude-r.yaml). This one-sided argument requires only necessary injectivity, whereas [necessary bijectivity](reversible-quantifier-observers.md), §2, supplies both inverse equations.

C5 makes current Inj(E) necessary by NI, ND_t and BF_t, as in the latter note, §3. Thus every currently injective operation has an admitted unqualified left inverse over C5. Whether a logical E has a *qualified* left inverse is an additional condition; (11) does not answer it.

### Current injectivity need not persist, even with necessary BF

For a direct individual counterexample, use the full action model on the poset

```math
P=\{*\}\sqcup\mathbb Z,
\qquad *<n\ (n\in\mathbb Z),
```

with the usual order on the integer part and singleton individuals. A proposition at * is an arbitrary subset of P. At integer n it is an arbitrary subset of T_n={m∈ℤ:m≥n}. Fullness admits every relational future truth profile. Transport restricts these profiles to the later coordinates; arbitrary profiles there extend by arbitrary earlier values, so every type transport is onto. The full action construction supplies C and all necessary BF and Functionality instances.

Define an observer at * by observing the identity arrow at * and n→n+1 at each future integer n, on arbitrary inputs at each such stage. These profiles are admitted by fullness. All observation arrows act onto at every type, so the same Boolean and all-future quantifier calculation as for the omega-chain shifts proves every full Good law. On current propositions it acts by inverse image under

```math
f(*)=*,\qquad f(n)=n+1.
\tag{14}
```

This f is a bijection of P. Thus E is currently bijective, and in particular injective, at *. At an integer n, however, its transported operation is the ordinary forward shift on T_n; it sends both {n} and Bottom to Bottom. Hence □Inj(E) is false at *. By (11), E has no admitted whole left inverse. This is an individual-operation counterexample, not an InjSep countermodel.

## 5. Omega shifts: BoxSep without C5 or injective separation

In the [full omega-chain model](omega-chain-surjective-observers.md), a proposition at n is p⊆T_n and

```math
(E_kp)(m)=p(m+k),\qquad k\ge0.
\tag{15}
```

Each E_k is admitted, Good for every finite list, and currently onto. These shifts separate at every relational output type, and at every future stage. The cited note proves the full composite qualification on arbitrary future predicates, not just its pointwise current shadow.

They also commute with native Box. At every future m and arbitrary input p⊆T_m,

```math
\begin{aligned}
m\in E_k(\Box p)
&\ \leftrightarrow\ T_{m+k}\subseteq p,\\
m\in\Box(E_kp)
&\ \leftrightarrow\ \forall j\ge m\ [j+k\in p].
\end{aligned}
\tag{16}
```

These conditions are identical. The comparison covers every future stage and arbitrary input there, establishing the whole operation identity. Thus the model satisfies full BoxSep and its separately boxed schema.

The same model fails C5. Moreover, every $`\mathrm{Good}_{\{t\}}`$ observer has the exact forward-coordinate representation proved in the cited note, §3; current injectivity forces that coordinate map, and hence the observer, to be identity. At n, identity cannot distinguish the distinct false propositions Bottom and {n+1}. Consequently InjSep(t,{t}) fails, and SplitMono fails with it.

Thus BoxSep implies neither C5, InjSep nor SplitMono, even over C+□BF+□Functionality. This does not conflict with the relative equivalence (10).

## 6. A root extension: BoxSep without necessary separation

Use the unchanged model in [Root truth-profile extension](root-truth-profile-surjective-separation.md), §§2–3. Its old two-object symmetric tail B has all bijections as arrows, and hence satisfies C5, BF and Functionality at every old object. Its distinguished old object X fails OS(t,∅). The new predecessor * has

```math
A_t=\{0,1\}\times B_t(X),
\tag{17}
```

and, at every relational type, an arbitrary root truth table paired with an old intension. The projections π_σ onto the old domains are onto. The cited construction verifies admitted lambda abstraction, contextual beta/eta, C's H-Logical-Equivalence schema, and necessary BF and Functionality at this root. We retain that entire higher-type model.

For each old arrow b:X→Z, use the newly selected root observer

```math
O_b=(h_b,I_B),\qquad
h_b(\varepsilon,q):=[b\in q].
\tag{18}
```

It is admitted because the root permits every current truth table paired with any old tt object. Its full Boolean laws follow from evaluation at b and the identity tail. For Q_σ and P_σ on an arbitrary root predicate, the root truth comparison quantifies over the images of ρ_σ(b)π_σ. These exhaust the target domain because π_σ is onto and b invertible. The old components agree because I_B preserves the operations. This proves the entire composite identities at every type; translated equality qualification follows over C. Thus O_b is Good_Δ for every finite Δ.

For p=(ε,q), put δ=1 if q=Top_B and δ=0 otherwise. The old equality judgment is an endpoint by C5, while the root judgment is actual equality of the pair. Hence

```math
\Box_*(\varepsilon,q)
  =(\varepsilon\land\delta,\delta\,\top_B).
\tag{19}
```

Here δTop_B denotes Top_B or Bottom_B according to δ. Equations (18)–(19) give

```math
O_b(\Box_*p)=(\delta,\delta\top_B)
            =\Box_*(O_bp).
\tag{20}
```

For the second equality, when δ=1 the evaluation h_b(p) is 1; when δ=0 the root conjunction in (19) is 0. The first truth functions in the two λp operations therefore agree on every root input. Their old components are the two Box composites with I_B and agree on every old input. Consequently (20) is a whole-operation identity in the root domains, not merely equality of current truth values.

The root identity observer distinguishes different first bits. If old tails differ, some b distinguishes them and O_b distinguishes the propositions' root truth values. This gives propositional BoxSep for every Δ; current Functionality gives the full typed lift. Nevertheless the accessible old X still fails OS(t,∅). Therefore

```math
\boxed{
\mathrm C+\mathrm{BoxSep}+\Box\mathrm{BF}
+\Box\mathrm{Functionality}
+\neg\Box\mathrm{OS}(t,\varnothing).}
\tag{21}
```

BoxSep implies OS instancewise by restriction. Thus (21) also gives ¬□BoxSep(t,∅). Native-Box qualification itself persists by NI on its operation identity; the failure concerns separation at the future point.

## 7. Exact comparisons established here

The following implications hold for the full schemas over H:

```math
\mathrm{Rev}\Longrightarrow\mathrm{BoxSep}
\Longrightarrow\mathrm{OS}+\Box\mathrm{BF}
+\Box\mathrm{Functionality}+.2.
\tag{22}
```

Rev supplies C5 and injective Good witnesses, so the first implication follows from (8). It is strict by the omega model. BoxSep⇒OS is strict: the all-maps ℕ/singleton model has even full SplitMono but fails necessary BF_e and BF_t, as proved in [Qualified left inverses](finite-block-symmetry-left-inverse.md), §7. Equation (7) makes BoxSep fail there.

That model has InjSep as well. Conversely the omega model has BoxSep but fails InjSep and SplitMono. Therefore BoxSep is incomparable with InjSep and with SplitMono over H, and already over C+current BF. This proves no strictness claim between SplitMono and InjSep themselves.

BoxSep is also incomparable with □OS, even over C+□BF. The root model in §6 gives BoxSep without □OS. For the other direction, the [linear and circular fibre model](linear-circular-fibre-left-inverse-gap.md) has C5+□OS and fails Rev. It also satisfies the internal condition that every admitted injective tt operation is onto. Under C5, an injective Good observer there is consequently bijective and has an admitted qualified two-sided inverse, by [necessary bijectivity](reversible-quantifier-observers.md), §§2–3. Thus its InjSep instances are exactly its Rev instances; the exhibited failed Rev instance refutes InjSep, and (10) refutes BoxSep. C5 supplies the common necessary-BF background.

The second implication in (22) is therefore strict as well. The linear/circular model has OS, necessary BF, necessary Functionality and .2, all supplied by its C5+□OS background, but fails BoxSep. Even that entire bundle does not recover native-Box separation.

Over C5 the full schemas form the strict chain

```math
\mathrm{Rev}\Longrightarrow
\mathrm{InjSep}\ \Longleftrightarrow\ \mathrm{BoxSep}
\Longrightarrow\mathrm{OS}.
\tag{23}
```

Both displayed implications are strict with C5 retained. The [finite-block model](finite-block-symmetry-left-inverse.md), §§1–6, has C5+SplitMono and fails Rev; its qualified left inverses give InjSep, and (10) gives BoxSep. The linear/circular model supplies the other strictness, as just proved.

No identification of InjSep with SplitMono, either outside or inside C5, follows from these comparisons. Equation (21) separately excludes the persistence conclusion □OS from BoxSep.

## 8. Sources

The native-Box theorem, the exact C5 equivalence, the one-sided description lemma, and the new model verdicts are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–7, unpaginated.

The fixed framework, NI, CBF, necessitation and Intensionality are Bacon and Dorr, *Classicism*, draft of 16 May 2023, §§1.3–1.5, pp. 13–18; §2.1, pp. 20–22. Their recorded [NI](../../source/topics/classicism/principles/identity-necessary-r.yaml), [BF](../../source/topics/classicism/principles/barcan-r.yaml), and [necessary Functionality consequence](../../source/topics/classicism/results/necessary-barcan-r-implies-necessary-functionality-r.yaml) provide the exact formulas and source locators.

The description term in §4 originates in Cian Dorr's proposition-output witness of 28 September 2026, retained with its attribution in the linked modalized-Plenitude record. The present one-sided inverse theorem and its proof are new applications, not claims attributed to that record.

The full action-model semantics used for the root-below-integers construction and omega chain are Bacon and Dorr, *Classicism*, §3.5, pp. 58–61; Appendix D, pp. 73–74, as recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). The higher-type root extension, symmetric tail and comparison-model proofs are the linked research notes, each with its own construction sources and status. The additional BoxSep verdicts above do not change their original proofs or claim new formal verification.
