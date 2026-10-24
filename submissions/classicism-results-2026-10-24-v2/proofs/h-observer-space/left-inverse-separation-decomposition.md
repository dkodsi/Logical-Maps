# Left-inverse separation: reversible witnesses or one true kernel element

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new normalization and decomposition: `misc`, this note, §§1–6, unpaginated. Existing patching and framework results are cited in §7.

Left-inverse separation has an exact local decomposition. Either reversible observers already separate, or a **single qualified inverse pair with a true kernel element** can convert every ordinary observer into a left-invertible observer with the same current truth profile. The conversion uses one fixed left inverse for every observer being converted.

The decomposition isolates a sufficient condition involving just one pair, and proves that this condition is necessary whenever left-inverse separation holds but reversible separation fails. The later [linear and circular fibre model](linear-circular-fibre-left-inverse-gap.md) settles C5+□OS⇒SplitMono negatively; the present theorem identifies the alternative missing at its failed finite-list instance.

## 1. Fixed background, list and output type

Work over C+BF, where BF is the Barcan schema. Only finitely many instances enter any application; BF_t is used to collect the final pointwise inverse identities. Fix a finite external qualification list Δ containing t. Use the full composite Good_Δ qualification from [Qualified right-inverse separation](split-inverse-logical-observers.md), §1. Both observers in an inverse pair are admitted and qualified for the same Δ. All equations between compositions below are identities of whole operations.

Write S_{τ,Δ}[Good], S_{τ,Δ}[SplitMono] and S_{τ,Δ}[Rev] for the corresponding separation sentences at relational output type τ. Their agreement clause universally quantifies over the argument tuple of τ. At τ=t this is ordinary material agreement between the observed propositions.

Define the following one-pair sentence:

```math
\begin{aligned}
K_\Delta:=\exists E^{tt}F^{tt}c^t\,[
&\mathrm{Good}_\Delta(E)\land
\mathrm{Good}_\Delta(F)\\
&\land F\circ E=I\land c\land Fc=\bot].
\end{aligned}
\tag{1}
```

Thus c is currently true while F sends it to the Bottom proposition, and E is a qualified right inverse of F. This is not merely the assertion that Fc is currently false. The identity Fc=Bottom is what permits the normalization. No separation principle occurs in K_Δ.

The main fixed-instance theorem is

```math
\boxed{
S_{\tau,\Delta}[\mathrm{SplitMono}]
\ \longleftrightarrow\
S_{\tau,\Delta}[\mathrm{Rev}]
\ \lor\
\bigl(S_{\tau,\Delta}[\mathrm{Good}]
\land K_\Delta\bigr).
}
\tag{2}
```

The disjunction is between two sentences for the **same fixed output type and finite list**. It is not an assertion that the full schema globally chooses one disjunct for every list.

## 2. One true kernel element normalizes every observer

Assume E,F,c witness K_Δ. For any admitted Good_Δ observer G, form the lambda term

```math
E_G(p):=(c\land Gp)\lor(\neg c\land Ep).
\tag{3}
```

The coefficients c,¬c are a Boolean partition. The existing full-operation Boolean-patching lemma makes E_G a Good_Δ observer. Fixed propositional guards add no quantifier type to the qualification list. This lemma operates under the stated C+BF background and supplies full composite identities, rather than just current material preservation.

Boolean preservation by F, Fc=Bottom and F∘E=I give, for every p,

```math
\begin{aligned}
F(E_Gp)
&=(Fc\land F(Gp))\lor(F(\neg c)\land F(Ep))\\
&=(\bot\land F(Gp))\lor(\top\land p)=p.
\end{aligned}
\tag{4}
```

Functionality at tt, available from the stated Barcan background, collects (4) into F∘E_G=I. Equivalently one can apply NI to the pointwise identities, collect with BF_t, and apply C's Intensionality. Neither method necessitates an optional premise.

Since c is currently true, propositional reasoning gives the entire current truth-profile agreement

```math
\forall p\,(E_Gp\leftrightarrow Gp).
\tag{5}
```

The same F is a qualified left inverse of every E_G constructed by (3). Admission is explicit: E_G is a lambda term in the already admitted parameters. No choice of inverse or family of witnesses is required.

Consequently K_Δ together with ordinary separation at any relational output type τ gives SplitMono separation at that same type and list. Given a distinguishing G and argument tuple, equation (5) preserves its two truth values. Equality gives the other direction of the separation biconditional.

In fact under K_Δ, ordinary, left-inverse and qualified right-inverse-of-this-fixed-F observers have exactly the same separating power, because every ordinary truth profile is realized by one of the E_G. This is a statement about realized truth profiles; it does not identify the observers as objects or claim that they are reversible.

## 3. Every left-inverse pair has a local opposite equation

Now assume only Good_Δ(E), Good_Δ(F) and F∘E=I. Put

```math
u:=\forall p^t\,[E(Fp)\leftrightarrow p].
\tag{6}
```

The proposition u is defined, not assumed true. The unconditional universal-instantiation theorem and C's Boolean identities imply

```math
u\land E(Fp)=u\land p
\qquad\text{for every }p.
\tag{7}
```

This order calculation is the same discharged logical argument used for the equalizer proposition in [the right-inverse proof](split-inverse-logical-observers.md), §2. It does not turn a conditional material equivalence into an identity by an unrestricted Logical Equivalence step.

Since t∈Δ, F's full Q_t and Boolean identities give

```math
\begin{aligned}
Fu
&=\forall p\,F(E(Fp)\leftrightarrow p)\\
&=\forall p\,[F(E(Fp))\leftrightarrow Fp]\\
&=\forall p\,[Fp\leftrightarrow Fp]=\top.
\end{aligned}
\tag{8}
```

If u is currently false, c₀:=¬u is currently true and F c₀=Bottom. The very same E,F,c₀ therefore witness K_Δ.

If u is true, (7) supplies the missing opposite equation exactly where the next construction needs it. It need not make E∘F=I globally.

## 4. A distinguishing witness with true u gives an involution

Suppose d is currently false, Ed is currently true, and u from (6) is currently true. Define

```math
c:=\neg d\land Ed\land u,
\qquad b:=Fc,
\qquad r:=\neg(c\lor b),
\tag{9}
```

and

```math
T(p):=(c\land Ep)\lor(b\land Fp)\lor(r\land p).
\tag{10}
```

The following calculations use identities throughout; the current-truth assumptions are needed only at the final distinguishing step.

First c≤Ed, so b=Fc≤F(Ed)=d. Also c≤¬d, hence b≤F(¬d)=¬Fd. It follows that b∧c=Bottom and c,b,r form a Boolean partition. Thus the full-operation patching lemma makes T Good_Δ for the original list.

On the c-region we have

```math
c\land Ec=\bot,
\qquad c\land Eb=c,
\qquad c\land Er=\bot,
\qquad c\land E(Fp)=c\land p.
\tag{11}
```

For the first equation, c≤Ed while Ec≤E(¬d)=¬Ed. For the second, Eb=E(Fc), and c≤u allows (7) at p=c. The third follows from Er=¬(Ec∨Eb) and the second. The last is (7) restricted further to c.

On the b-region we have

```math
b\land Fc=b,
\qquad b\land Fb=\bot,
\qquad b\land Fr=\bot,
\qquad F(Ep)=p.
\tag{12}
```

The first is b=Fc. For the second, b≤d implies Fb≤Fd, while b≤¬Fd was already shown. The third follows from r≤¬c and b=Fc. The last is the given whole inverse equation evaluated at p.

Expand T(Tp) along c,b,r. On c, (11) removes the E(Ep) and E(p) branches; the remaining term is c∧E(Fp)=c∧p. On b, (12) removes the F(Fp) and F(p) branches; the remaining term is b∧F(Ep)=b∧p. On r, the outer identity branch gives r∧Tp=r∧p. Therefore

```math
\forall p\,[T(Tp)=p].
\tag{13}
```

NI, BF_t and Intensionality, or the resulting Functionality at tt, collect (13) into the whole-operation identity T∘T=I. Finally c is currently true, so Td has the same truth as Ed and is true. TBottom is false by Boolean qualification. Thus T is a qualified involution detecting the original false d.

We have proved a local alternative for every distinguishing left-invertible observer: either its u is true and it yields a distinguishing involution, or its u is false and the same pair supplies K_Δ. The involution alternative concerns the chosen distinction; it does not say that every such E is itself reversible.

## 5. The global case split for one separation sentence

Assume S_{τ,Δ}[SplitMono]. Forgetting the inverse restriction gives S_{τ,Δ}[Good]. If S_{τ,Δ}[Rev] already holds, the first disjunct in (2) follows.

Otherwise there are X≠Y of output type τ such that every qualified reversible observer agrees materially on X and Y at **every argument tuple**. SplitMono separation supplies E,F with F∘E=I and a tuple $`\bar a`$ at which $`E(X\bar a)`$ and $`E(Y\bar a)`$ have different truth values. Let

```math
d:=(X\bar a)\mathbin{\triangle}(Y\bar a)
\tag{14}
```

be their Boolean symmetric difference. Boolean preservation makes Ed true. The identity observer is reversible, so the assumed reversible agreement at this very tuple makes d currently false.

Form u from (6). If u were true, §4 would supply a qualified involution T with Td true. Its Boolean identities would make $`T(X\bar a)`$ and $`T(Y\bar a)`$ differ in truth, contradicting the chosen reversible agreement. Thus u is false, and §3 supplies K_Δ. This proves the second disjunct of (2).

Conversely, reversible separation immediately gives SplitMono separation. The other disjunct supplies it by §2. This proves (2), including its typed scope.

An equivalent useful formulation is

```math
\neg K_\Delta\ \longrightarrow\
\bigl(S_{\tau,\Delta}[\mathrm{SplitMono}]
\leftrightarrow S_{\tau,\Delta}[\mathrm{Rev}]\bigr).
\tag{15}
```

Here ¬K_Δ means that no qualified pair has a currently true kernel element of the stated form. It does not assert that every left-invertible observer is a two-sided inverse. Formula (15) only replaces its distinguishing action by an involution.

## 6. Full-H scope and necessary separation

The full logical-separation theorem supplies C+BF from H+OS. Functionality then identifies propositional and full typed separation for any fixed observer class and list, as in [Typed separation and Classicism](typed-separation-and-classicism.md). Consequently (2) gives the following exact reformulation over H:

```math
\boxed{
\text{full SplitMono}
\ \longleftrightarrow\
\text{full OS}
\ +\
\bigl\{
S_{t,\Delta}[\mathrm{Rev}]\lor K_\Delta:
\Delta\text{ finite},\ t\in\Delta
\bigr\}.
}
\tag{16}
```

The braces denote an external schema. In the forward direction full SplitMono gives full OS and hence the background needed for (2). In the reverse direction full OS gives C+BF, each disjunction supplies propositional SplitMono separation, and Functionality lifts it to all relational output types. An arbitrary requested list can first be enlarged by t and then weakened back, so the restriction t∈Δ loses no full-schema instance.

In particular, if K_Δ holds at every finite list containing t, full OS suffices for full SplitMono. A separate pair may witness each list. No infinitely qualified observer or common pair across all types has been introduced.

Necessary ordinary separation does not by itself appear in this proof. In the background C5+□OS, the theorem says that SplitMono at a requested finite list is equivalent to S_{t,Δ}[Rev]∨K_Δ. The later [linear and circular fibre model](linear-circular-fibre-left-inverse-gap.md), §§5–9, satisfies that background but fails SplitMono at its explicit Δ₀. Consequently both disjuncts fail there. Thus C5+□OS does not supply the additional admitted inverse structure identified by this theorem. A current bijection, an external section or a modal existence claim cannot be substituted for the admitted whole-operation equations in (1).

This decomposition also applies to the earlier strict models. Where full SplitMono holds but a fixed Rev instance fails, (2) supplies a true kernel pair for that list. The finite fork has ordinary separation but fails SplitMono, so it can have neither that reversible separation instance nor the corresponding K_Δ. The linear/circular model shows that this latter configuration can also occur under C5+□OS.

## 7. Sources

The one-pair normalization, the u-guarded local involution, the fixed-instance disjunction and the full-schema reformulation are new arguments by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated.

The Boolean-patching lemma is in [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §4. The discharged instantiation argument for an equalizer proposition and the use of BF_t to collect whole inverse identities are in [Qualified right-inverse separation](split-inverse-logical-observers.md), §§2–4. The present argument uses the opposite inverse orientation and adds the true-kernel normalization; it does not infer the new result merely by interchanging E and F in the earlier separation theorem.

Full-H recovery and typed lifting are in [Typed separation and Classicism](typed-separation-and-classicism.md), §§2–7. The model comparisons are [Finite-pinning models with qualified left-inverse separation](finite-block-symmetry-left-inverse.md) and [Full three-object fork](fork-one-sided-inverse-separation.md). The underlying rules of C, NI and Intensionality are those of Bacon and Dorr, *Classicism*, draft of 16 May 2023, §1.5, pp. 16–18. These sources supply the framework and earlier lemmas, not the new decomposition.
