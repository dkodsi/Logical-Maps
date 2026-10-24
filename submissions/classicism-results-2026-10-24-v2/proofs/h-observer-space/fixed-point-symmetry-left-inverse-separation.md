# Fixed-point symmetry: left-inverse separation without persistence

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the fixed-point criterion and new observer verdict: `misc`, this note, §§1–6, unpaginated. The retained symmetric model and earlier observer results are attributed in §7.

Infinitely many points fixed by a source symmetry group give one admitted qualified inverse pair with a true kernel element. Consequently, in the symmetric finite-pinning framework, ordinary separation at such a source already yields left-inverse separation. A trivial source symmetry group supplies ordinary separation as well.

Applying this criterion to the existing qualitative-contrast model at its trivial-symmetry object gives

$$
\mathrm{C5}+\mathrm{SplitMono}+\Box\mathrm{BF}
+\Box\mathrm{Functionality}
+\neg\Box\mathrm{OS}.
\tag{1}
$$

In particular C5+SplitMono implies neither necessary OS nor necessary SplitMono. The positive separation verdict has full relational output scope and every finite external qualification list. The boxed OS failure is already witnessed by the propositional Boolean-separation instance at the empty list.

## 1. Framework and the exact sufficient condition

Use a symmetric ideally-full action model whose arrows are all bijections between the underlying objects, whose pinning ideals are the finite subsets, and whose designated symmetry group at an object X is G_X. Relational domains contain exactly the symmetric finitely pinned intensions. The cited construction supplies C. All arrows act bijectively at every type, so C5, BF and Functionality hold throughout the model.

Assume a source object X has an external sequence

$$
x_0,x_1,x_2,\ldots
\tag{2}
$$

of pairwise distinct individuals, each fixed by every member of G_X. The argument needs precisely this sequence; it makes no object-language assertion of an admitted enumeration. In particular the hypothesis holds at a countably infinite source with trivial designated symmetry group. Other objects and their symmetry groups are unrestricted within the stated model framework.

For a finite type list Δ, Good_Δ has the full Boolean and quantifier composite identities and translated equality clauses used throughout the observer notes. Recall the true-kernel condition

$$
\begin{aligned}
K_\Delta:=\exists E^{tt}F^{tt}c^t\,[
&\mathrm{Good}_\Delta(E)\land\mathrm{Good}_\Delta(F)\\
&\land F\circ E=I\land c\land Fc=\bot].
\end{aligned}
\tag{3}
$$

The construction below supplies the same admitted E,F,c for every finite Δ. This is a semantic fact about the witnesses, not an infinitary qualification formula.

## 2. The countable charts and the two observer profiles

Let ν₀=id_X. For n>0 let ν_n swap x₀ and x_n and fix all other individuals. Put

$$
\alpha_n=\nu_{n+1}\nu_n^{-1}.
\tag{4}
$$

Each α_n commutes with G_X: it is supported on points fixed individually by that group. Define pairwise disjoint sets of self-arrows

$$
C_n=\{h:X\to X:h(x_0)=x_n\}.
\tag{5}
$$

They are all pinned by {x₀} and are invariant under postcomposition by G_X. Moreover α_n maps C_n into C_{n+1} by postcomposition, and α_n^{-1} maps C_{n+1} into C_n. The complement of their union, including all arrows to other objects, is left unchanged in the construction.

For every outgoing h:X→Y choose the following observation arrows, whose source is Y:

$$
a_h=
\begin{cases}
\alpha_n^{-1},&h\in C_{n+1},\\
\mathrm{id}_Y,&\text{otherwise},
\end{cases}
\qquad
b_h=
\begin{cases}
\alpha_n,&h\in C_n,\\
\mathrm{id}_Y,&\text{otherwise}.
\end{cases}
\tag{6}
$$

Define entire exponential truth profiles, for every proposition q at Y, by

$$
E(h,q)\Longleftrightarrow a_h\in q,
\qquad
F(h,q)\Longleftrightarrow b_h\in q.
\tag{7}
$$

Both profiles are {x₀}-pinned. If parallel h,h′ agree at x₀, they select the same branch and the same observation arrow, so (7) agrees for every input q.

They also satisfy target symmetry. At target X, for μ∈G_X, the chart of μh is the chart of h, and μ commutes with its observation arrow s=a_h or b_h. The transport equation and proposition symmetry give

$$
s\in\rho_t(\mu)q
\ \Longleftrightarrow\ s\mu\in q
\ \Longleftrightarrow\ \mu s\in q
\ \Longleftrightarrow\ s\in q.
\tag{8}
$$

On the complement the observation arrow is the identity, and the same calculation uses only proposition symmetry. At a different target Y, the entire branch is identity observation, which is likewise symmetric under G_Y. Thus ideal fullness admits E and F. Countably many cases in the external definition do not require an infinite pin: their selected value depends on the one point h(x₀).

## 3. The whole inverse equation and the true kernel element

For every outgoing h we have the arrow identity

$$
a_{b_hh}\,b_h=\mathrm{id}_{\mathrm{target}(h)}.
\tag{9}
$$

If h∈C_n, then b_h=α_n and b_hh∈C_{n+1}, where a_{b_hh}=α_n^{-1}. If h lies outside all charts, both observations are identity and it remains outside the charts. These cases exhaust all outgoing arrows. The E branch on C₀ is never used in this round trip.

To check the whole operation identity rather than only current values, take any future arrow r:X→Y, arbitrary q∈D_t(Y), and further arrow l:Y→Z. Let E_r and F_r be the transported observers. Application and transport give

$$
\begin{aligned}
l\in F_r(E_rq)
&\Longleftrightarrow
a_{b_{lr}lr}\,b_{lr}\,l\in q\\
&\Longleftrightarrow l\in q,
\end{aligned}
\tag{10}
$$

where (9) is applied to h=lr. This holds for every future input and coordinate. Hence F∘E=I as an identity of admitted whole operations.

Let c be the proposition C₀, false on all other-target arrows. It is symmetric and {x₀}-pinned, hence admitted. The identity arrow belongs to C₀, so c is currently true at X. For every outgoing h,

$$
h\in Fc\quad\Longleftrightarrow\quad b_hh\in C_0.
\tag{11}
$$

The right side never holds: each C_n maps into C_{n+1}, and the complement remains outside the charts. Thus Fc=Bottom as a proposition identity, not merely as current falsity.

## 4. Full logical qualification and the normalization consequence

Every observation arrow in (6) is a bijection. For E, at a future arrow r and input p, its output at a further coordinate l is determined by membership of a_{lr}l in p. Boolean set operations and endpoints therefore commute with E at every future input. At a quantifier type σ, the two sides of the commutation law compare quantification over the whole σ-domain at the target of a_{lr} with quantification over its image under ρ_σ(a_{lr}). These agree because that type action is onto, with the inverse arrow supplying its inverse. The existential calculation is identical with ∃. The same proof applies to F and b_{lr}.

The calculations cover all future inputs, so they give full composite identities. Translated equality clauses follow from Boolean qualification over C; in this groupoid they can also be checked because equality judgments are endpoints. Hence E and F are Good_Δ for every finite Δ. Together with (10)–(11), they witness K_Δ at X.

The [true-kernel normalization theorem](left-inverse-separation-decomposition.md), §2, now has a useful uniform application. For any admitted Good_Δ observer G, the admitted term

$$
E_G(p)=(c\land Gp)\lor(\neg c\land Ep)
\tag{12}
$$

is Good_Δ, satisfies F∘E_G=I, and has exactly G's current truth profile, since c is true. The same F works for every G. Thus ordinary and qualified left-inverse observers have the same current separating power at X, at each fixed list and relational output type. In particular, full OS at this source implies full SplitMono. The fixed-point hypothesis alone does not claim ordinary separation for a general G_X.

## 5. A trivial source group supplies ordinary separation too

Suppose now G_X is trivial. For any outgoing arrow d:X→Y define an observer O_d by the profile

$$
O_d(h,q)\quad\Longleftrightarrow\quad
\begin{cases}
d\in q,&\mathrm{target}(h)=X,\\
\mathrm{id}_{\mathrm{target}(h)}\in q,&\text{otherwise}.
\end{cases}
\tag{13}
$$

In the first branch q is a proposition at X, so membership of d is well typed. This entire profile is empty-pinned: for parallel h,h′ the answer on each fixed input q is the same. The first branch has no nontrivial target-symmetry obligation, and every other branch is identity observation. Hence O_d is admitted.

Each selected observation arrow is a bijection, so the all-future calculation of §4 gives every full Boolean and quantifier identity for O_d. At the identity of X, its truth profile reads membership of d. Distinct propositions differ at some outgoing d, so these observers separate them. Functionality lifts this to every relational output type. Therefore full OS holds at every trivial-symmetry source in this framework.

If X also has the sequence (2), §§2–4 then give full SplitMono. Equivalently, (12) turns every O_d into a qualified left-invertible observer with the same current truth profile. The arrow d and the enumeration used for the fixed charts are external ingredients in individual admitted profiles; no internal choice of a family of observers is asserted.

## 6. Qualitative contrast: C5 does not supply persistence

Retain the exact [qualitative-contrast model](../../source/topics/classicism/models/symmetric-qualitative-contrast.yaml), changing only its evaluation point to W₁. Its objects W₀,W₁ are copies of ℕ; arrows are all bijections; pinning ideals are finite sets; G_{W₀} is the full permutation group, while G_{W₁} is trivial. Section 5 applies at W₁, and any enumeration of that object supplies (2). Hence full SplitMono holds there. The base model already supplies C5 and necessary BF and Functionality.

At W₀, Boolean observer separation fails. The existing [countermodel proof](../observer-countermodel.md), §§2–4, shows that no admitted Boolean observer can accept the nonbottom proposition consisting of the arrows ending at W₁. It is currently false at W₀, so its agreement with Bottom refutes the propositional Boolean-separation sentence. This is the OS instance at output t and empty quantifier list.

W₀ is accessible from W₁. Thus that closed OS instance is not necessary at W₁, proving (1). Necessary full SplitMono would imply necessary full OS by forgetting the qualified inverse witnesses in each instance, so it fails as well. The implication C5+SplitMono⇒□OS is therefore false, as is C5+SplitMono⇒□SplitMono.

Combining this model with [linear and circular fibre orders](linear-circular-fibre-left-inverse-gap.md) proves an exact relative comparison: over C5, SplitMono and □OS are incomparable. This model supplies SplitMono without □OS; the linear/circular model supplies □OS without SplitMono. Both retain full typed schemas and identify a particular failed finite instance. No inference is made from the earlier non-C5 all-maps countermodel.

## 7. Sources

The fixed-point chart construction, uniform K_Δ witnesses, trivial-source observer criterion and new SplitMono verdict at W₁ are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–6, unpaginated. The construction adapts the arbitrary-future left-inverse calculation of [Finite-pinning models with qualified left-inverse separation](finite-block-symmetry-left-inverse.md), §§2–5, and applies [True-kernel normalization](left-inverse-separation-decomposition.md), §2.

The symmetric ideally-full framework is Cian Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p. 8; §3.1, p. 9; Lemma 21, p. 10, as recorded in [Symmetric ideally-full models](../../source/topics/classicism/groups/symmetric-ideally-full.yaml). The retained qualitative-contrast construction is Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, p. 79, final construction. These sources supply the model, not the new observer verdict.

The evaluation at W₁ and its necessary-OS failure were established in [Local and necessary observer separation](../local-observers.md), §§2–5. Its ordinary-separation verdict is reproved here by the profiles (13); the new claim is the qualified left-inverse strengthening and its reusable sufficient condition.
