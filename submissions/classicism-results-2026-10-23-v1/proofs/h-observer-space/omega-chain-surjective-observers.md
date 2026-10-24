# Full omega-chain: surjective logical observers without admitted inverses

By OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. Direct source for the new observer representation and verdicts: `misc`, this note, §§1–5, unpaginated. The existing full action-model construction and earlier omega-chain verdicts are attributed in §6.

In the full omega-chain model, $\operatorname{Good}_{\{t\}}$ observers are exactly the inverse-image operations of maps f satisfying f(m)≥m. Such maps are called forward coordinate maps here; they need not be nondecreasing. Shifts give surjective observers which separate at every future stage. An injective logical observer must be the identity. This proves

$$
\mathrm C+\Box\mathrm{BF}+\Box\operatorname{Atomicity}_t
+\Box\mathrm{SurjSep}
\ \not\Longrightarrow\ \mathrm{C5},\quad\mathrm{SplitMono}.
\tag{1}
$$
SurjSep means full typed separation by currently surjective Good observers, with every finite external qualification list and full composite preservation identities. A box on a schema denotes the separate boxes of its closed instances. The failed SplitMono instance is already propositional, at Δ={t}. The model also shows directly that a necessarily surjective logical observer need not have any admitted right inverse over C.

## 1. The full action model and its type transports

Take objects n∈ℕ, with one arrow n→m when n≤m, and singleton individuals. Use the full relational action-model domains. This is the existing omega-chain construction from [Two upper observer models](../observer-lattice-models.md), §1. At n,

$$
D_t(n)=\mathcal P(T_n),\qquad T_n=\{m:m\ge n\}.
\tag{2}
$$
Truth is membership of n, Boolean operations are set operations, and proposition transport restricts to a later tail. Fullness means that every relational truth profile on future stages and the admitted argument tuples there is an admitted intension. At every relational type, transport along n→j forgets the earlier stages of such a profile. An arbitrary profile on stages m≥j therefore extends by assigning arbitrary truth values on the omitted stages. Thus every forward type action is onto. At type e the transport is the unique map between singletons.

The full action construction supplies C. Surjective type transport gives BF at every stage, and hence Functionality there. The powerset proposition algebras give Atomicity_t at every stage. Consequently necessary BF, necessary Functionality and necessary Atomicity_t hold. These are the already established positive properties of this model; the new work below concerns its logical observers.

## 2. Shift observers are admitted, qualified and surjective

Fix an external natural number k≥0. At n define an observer E_k^n by its entire future profile: at an arrow n→m and an arbitrary q∈D_t(m), its truth value is

$$
E_k^n(m,q)\quad\Longleftrightarrow\quad m+k\in q.
\tag{3}
$$
Fullness admits this profile. It specifies the observer on every future input, not only current propositions. Transport of E_k^n to m gives E_k^m, and application yields

$$
E_k^n(p)=\{m\ge n:m+k\in p\}.
\tag{4}
$$
For any q⊆T_n the admitted proposition p={m+k:m∈q} is a preimage under (4). Its membership on the omitted k initial positions is immaterial. Thus E_k^n satisfies the current internal formula ∀q∃p(E_k^n p=q). The same reasoning applies after every transport, so the fixed observer is also necessarily onto. This does not choose an admitted inverse operation.

Equation (4) preserves every Boolean operation and both endpoints. For the full universal-quantifier law at type σ, let m≥n and F∈D_{σt}(m) be an arbitrary future input. Put j=m+k and let F_j be its transport to j. The truth of E_k^m(∀_σF) at m says

$$
\forall y\in D_\sigma(j)\quad F_j(y)\text{ is true at }j.
\tag{5}
$$
The truth of ∀_σ(λx.E_k^m(Fx)) at m says

$$
\forall x\in D_\sigma(m)\quad
F_j\bigl(\rho_\sigma(m\to j)x\bigr)\text{ is true at }j.
\tag{6}
$$
These agree because ρ_σ(m→j) is onto. Replacing both universal quantifiers by existential ones proves the existential law. Since this comparison covers every future stage and every admitted F there, it proves the identity of the whole composite λF operations. The Boolean identities follow by the same all-stage test. The translated equality clauses follow from Boolean qualification over C; the shifts need not reflect identity. Thus E_k^n is Good_Δ for every requested finite Δ.

If p≠q in D_t(n), choose m≥n where their memberships differ and take k=m−n. Then E_k^n p and E_k^n q differ in current truth. These qualified surjective observers separate propositions. For any relational output type, Functionality supplies an argument tuple at which distinct relations have distinct proposition values, and a shift separates those values. This gives full typed SurjSep for every finite list. It holds at every object, so every closed instance is also necessary. No infinitely qualified observer formula or common object-language family of all shifts is required.

## 3. Every Good_{t} observer is a forward coordinate map

Let E be an arbitrary $\operatorname{Good}_{\{t\}}$ observer at n. Write E_m for its transport to m≥n. Its current Boolean truth test

$$
h_m(q):=[m\in E_m(q)]\qquad(q\subseteq T_m)
\tag{7}
$$
is a Boolean homomorphism to {0,1}, preserving both endpoints. We show it is evaluation at one point of T_m. Equivalently, the ultrafilter of propositions it accepts is principal.

Suppose no singleton is accepted. Boolean preservation then rejects every finite subset of T_m and accepts every cofinite subset. Fullness admits a predicate F:tt at m with the following truth profile at every j≥m and x⊆T_j:

$$
F(j,x)\quad\Longleftrightarrow\quad x\ne\{j\}.
\tag{8}
$$
For a fixed p⊆T_m, its value F(p) is true at j exactly when p∩T_j≠{j}. It can fail only at the maximum of a nonempty finite p. Hence every F(p) is cofinite and is accepted by h_m. But ∀p Fp is Bottom: at every stage j the current argument x={j} falsifies F. Thus

$$
\forall p\,E_m(Fp)\text{ is true at }m,
\qquad
E_m(\forall p\,Fp)\text{ is false at }m,
\tag{9}
$$
contradicting the transported full Q_t law. Some singleton {f(m)} is therefore accepted. It is unique, and Boolean preservation now gives h_m(q)=1 exactly when f(m)∈q. Necessarily f(m)≥m.

Application naturality consequently gives, for every current p⊆T_n,

$$
E(p)=f^{-1}[p],\qquad
f:T_n\to T_n,\quad f(m)\ge m.
\tag{10}
$$
This also specifies E on arbitrary future arguments through (7), so it identifies the whole admitted observer. Conversely, every external map f with f(m)≥m supplies an admitted profile E_f(m,q):=[f(m)∈q]. The Boolean proof and (5)–(6), now using j=f(m), show that E_f satisfies all full quantifier identities. Thus the correspondence is exact. In this particular model, $\operatorname{Good}_{\{t\}}$ already equals the class qualified at every finite list containing t. This is a semantic classification, not a general reduction of qualification over H or C.

## 4. Injectivity and the absence of admitted inverses

For the inverse-image map in (10), current injectivity of E is equivalent to surjectivity of f. If f misses a point j, the distinct propositions ∅ and {j} have the same image. Conversely, if f is onto, any point at which p and q differ has a preimage and distinguishes E(p) from E(q).

An onto map f:T_n→T_n satisfying f(m)≥m must be the identity. Surjectivity at n forces f(n)=n. If the assertion has been proved up to m−1, the preimage of m can be neither an earlier point nor a later one, so f(m)=m. Ordinary external induction completes the proof. Hence

$$
E\text{ Good}_{\{t\}}\text{ and currently injective}
\quad\Longrightarrow\quad E=I.
\tag{11}
$$
Any admitted whole left inverse F∘E=I makes E currently injective, even if F is unqualified. Thus the only $\operatorname{Good}_{\{t\}}$ observer with an admitted left inverse is I. At n, the distinct propositions ∅ and {n+1} are both false, and I does not distinguish their truth. The propositional SplitMono separation instance for Δ={t} therefore fails at every node. The statement uses neither a presumed global inverse nor an identification of internal and external finiteness.

Current surjectivity of E_f, by contrast, is equivalent to injectivity of f. If f(m)=f(l) with m≠l, no output can contain exactly one of m,l. If f is injective, an arbitrary output q⊆T_n has preimage f[q]. Positive shifts are examples, so current onto does not imply injective here.

There is a sharper admission obstruction. If f(j)>j at any future stage j, E_f has no admitted whole right inverse R, qualified or otherwise. Indeed, the truth at j of E_f(Rp) is the truth of Rp at f(j), which by naturality depends only on the transported input p∩T_{f(j)} and the transported R. Two admitted propositions which differ at j but agree on T_{f(j)} must therefore give the same result. The identity operation distinguishes them at j. This contradicts E_f∘R=I, whose identity would also hold after transport to j. In particular every positive shift lacks an admitted right inverse, despite being necessarily onto and fully qualified.

## 5. Exact separation consequences and comparisons

At n, a={n} differs from Bottom but becomes Bottom after transport to n+1. Thus ND_t, and hence C5, fails. Together with §§1–4 this proves (1). Full Rev also fails, both because it implies C5 and because its observers form a subclass of the left-invertible observers.

The distinction sharpens the surjective-observer theorem: [Canonical qualified sections](surjective-logical-observers.md), §§2–5, proves over C5 that surjective Good observers have admitted qualified right inverses, and that their separation is equivalent to Rev. Here even necessary surjectivity does not supply an admitted right inverse, and full SurjSep does not recover C5. The extra C5 premise cannot be omitted from either conclusion.

Globally, with the full schemas over H, the elementary implications are

$$
\mathrm{Rev}\ \Longrightarrow\ \mathrm{SurjSep}
\ \Longrightarrow\ \mathrm{OS}.
\tag{12}
$$
Both are strict. The present model has SurjSep and fails Rev. The [linear and circular fibre model](linear-circular-fibre-left-inverse-gap.md) has C5+□OS and fails Rev; the C5 surjective-separation equivalence therefore makes SurjSep fail there too.

SurjSep and SplitMono are incomparable even over the common background C+□BF+□OS. This model has SurjSep and fails SplitMono. Conversely, the C5 finite-block model in [Qualified left inverses](finite-block-symmetry-left-inverse.md), §§1–6, has separately necessary full SplitMono but fails Rev, and therefore fails SurjSep by the same C5 equivalence. Its C5 supplies □BF, and its □SplitMono supplies □OS. This does not assert a C5-relative incomparability: within C5, SurjSep is equivalent to Rev and hence implies SplitMono.

## 6. Sources

The shift observers, their exact forward-map classification and the new surjectivity/inverse verdicts are by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026: direct source `misc`, this note, §§1–5, unpaginated. The diagonal predicate (8) is adapted from the finite-image obstruction in [Two upper observer models](../observer-lattice-models.md), §1; the principality and complete observer classification are proved here.

The semantic framework is Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61; Appendix D, pp. 73–74, as recorded in [Full action models](../../source/topics/classicism/groups/full-action-models.yaml). Its all-type surjective-transport Barcan criterion is Proposition 3.24(ii), recorded in [Full epic Barcan](../../source/topics/classicism/arguments/full-epic-barcan.yaml). The specific omega-chain model and its necessary Atomicity_t and necessary BF were already established in the cited upper-model note; the present observer verdicts are not attributed to the source paper.

The Good definition and full typed separation convention are [Logical observer separation and its hierarchy](../logical-observer-hierarchy.md), §§1–4. The other comparison models and the C5 surjective equivalence retain the proofs and scope of the linked notes.
