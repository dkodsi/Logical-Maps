# Logical separation with contingent Barcan

Ordinary mathematical research by OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026. The new observer argument has direct source `misc`, this note, §§2–5, unpaginated. The underlying action model and its contingent-Barcan verdict are already recorded and retain their original source attribution.

**Result.** Ordinary full typed logical observer separation does not entail necessary BF. The existing finite-support action model on ℕ and a singleton, evaluated at ℕ, satisfies full OS while BF fails at its accessible singleton. The recorded failure includes both necessary all-type BF and necessary BF at t.

The proof uses current material observer laws followed by the unconditional C guard construction. It does not assume that separation persists, that a raw evaluation observer has the same future evaluation profile, or that an optional observer qualification may be necessitated.

## 1. The recorded model and the qualification

Use the [finite-support two-object all-maps model](../../source/topics/classicism/models/finite-support-two-object-all-maps.yaml). Its objects are W₀=ℕ and W₁={0}, its arrows are all functions between these objects, and each object carries the ideal of finite subsets. The model is ideally full in the sense of Classicism, Appendix D. Evaluate at the identity of W₀.

The record attributes this construction and the original BF/necessary-BF separation to Bacon and Dorr, *Classicism*, draft of 16 May 2023, Appendix D, p. 79, paragraph beginning “One particularly interesting result”. The [construction group](../../source/topics/classicism/groups/finite-support-two-object.yaml) identifies its C soundness with Appendix D, Proposition D.4. The following properties are part of that recorded construction:

1. It is a C model.
2. It is **extensionally full**: every set of currently admitted proposition objects is the current truth extension of an admitted observer of type tt. This is the `extensionally-full` condition in [conditions](../../source/topics/classicism/conditions.yaml), explicitly met by the model. Codomain-dependent intensions supply these realizers; no restriction to definable subsets is imposed.
3. Every proposition is pinned by a finite subset of the source individual domain. Two arrows with the same codomain that agree on such a pin give the same truth value to that proposition.
4. Transport acts functorially at every admitted type and commutes with the logical interpretation and application.

For each finite external type list Δ, use the full Boolean and universal/existential composite identities in Good_Δ. Over C the translated equality clauses follow from Boolean preservation, so they require no separate semantic argument here. Endpoint-fixing clauses, if included, also follow for the normalized observers. This is the ordinary complete logical qualification from [Typed separation and Classicism](typed-separation-and-classicism.md), §§3–4, with no reversibility, endpoint-valuedness or finite-image restriction.

## 2. A sufficient action-model criterion

Fix an object W in a C action model and a finite Δ. Assume:

- every subset of D_t(W) is realized as the current truth extension of an admitted tt object;
- whenever p≠q in D_t(W), there is an arrow g:W→V distinguishing their transported truth values such that g_σ:D_σ(W)→D_σ(V) is onto for every σ∈Δ.

Then propositional full-composite Good_Δ separation holds at W.

To prove it, choose such a g for the given distinct p,q. Let

$$
U_g:=\{r\in D_t(W):g_t(r)\text{ is true at }V\}.
$$

Extensional fullness gives an admitted observer O_g with exactly this **current truth extension**:

$$
O_g(r)\text{ is true at }W
\quad\Longleftrightarrow\quad
g_t(r)\text{ is true at }V.
\tag{1}
$$

Equation (1) specifies truth, not the output proposition object. It does not assert any equation for the transported observer g(O_g), or for O_g at other arrows.

The ordinary Boolean truth clauses at V show that O_g materially preserves negation, conjunction and disjunction at W. For a listed σ and any F∈D_{σt}(W), its universal law is the following calculation:

$$
\begin{aligned}
O_g(\forall_\sigma F)\text{ is true at }W
&\Longleftrightarrow
\forall y\in D_\sigma(V),\ (g_{\sigma t}F)(y)\text{ is true at }V\\
&\Longleftrightarrow
\forall x\in D_\sigma(W),\ (g_{\sigma t}F)(g_\sigma x)
                                      \text{ is true at }V\\
&\Longleftrightarrow
\forall x\in D_\sigma(W),\ O_g(Fx)\text{ is true at }W.
\end{aligned}
\tag{2}
$$

The middle equivalence uses exactly the surjectivity of g_σ. The final step uses naturality of application and (1). Replacing every universal quantifier by an existential gives the corresponding existential law. Thus O_g satisfies the finite material Boolean/quantifier qualification K_Δ at W, and it distinguishes p,q there.

### The guard supplies the full composite identities

The admitted term

$$
O_g^\#(r):=
(K_\Delta(O_g)\land O_g(r))
\lor(\neg K_\Delta(O_g)\land r)
\tag{3}
$$

satisfies the requested full composite laws in C. For an arbitrary observer variable O, H proves each material preservation law for the term O^# unconditionally: if K_Δ(O), use O's corresponding law; otherwise O^# agrees in truth with identity. The qualification is closed over each law's inputs, so it remains constant throughout the relevant input quantifiers. C's Logical Equivalence applied to this unconditional H equivalence, abstracting O and all law inputs, identifies the complete composite operations. Application to O_g gives their required identities. This is the finite guard theorem in [Typed separation and Classicism](typed-separation-and-classicism.md), §4, and [Observer lattice](../observer-lattice.md), §1.

Translated equality qualification then follows from C and Boolean preservation. The same unconditional truth calculation gives endpoint fixing if it is retained in the definition of Good.

At W, K_Δ(O_g) is true by (2), so (3) has exactly the current truth profile of O_g. It still distinguishes p,q. This proves the stated propositional separation instance. Neither the qualification nor an arbitrary current material theorem was necessitated.

If this criterion holds for every finite Δ, it gives every propositional logical separation instance. Those instances imply all BF instances by the usual separation-from-Top proof. C plus BF gives Functionality, and hence full typed OS by [the typed factorization theorem](typed-separation-and-classicism.md), §2. For one fixed finite Δ alone, retain an explicit Functionality premise if full relational separation at arbitrary types is wanted.

## 3. Split epimorphisms supply the needed surjectivity

Suppose an arrow g:W→V has a section s:V→W with g∘s=id_V. Functoriality at every type gives

$$
g_\sigma\circ s_\sigma=\mathrm{id}_{D_\sigma(V)}.
$$

Therefore g_σ is onto at every admitted type. This includes all higher relation types, not just individuals. No induction asserting surjectivity of arbitrary function-space maps is needed.

At W₀=ℕ, every surjection g:ℕ→ℕ has a section in the all-maps category. For example, choose the least preimage of each natural number. The unique arrow c:ℕ→{0} also has a section, any arrow i_n:{0}→ℕ selecting n. Thus both kinds of arrow supply all the surjectivities required in §2.

## 4. These arrows distinguish every proposition pair at ℕ

Let p,q be distinct propositions at W₀. Proposition objects in the action model are their truth intensions, so some outgoing arrow h distinguishes them. Choose finite pins S_p,S_q, and put S=S_p∪S_q.

If h has codomain W₁, it is the unique arrow c, which is already split epic.

If h has codomain W₀, extend its restriction h|_S to a surjection g:ℕ→ℕ. Such an extension exists because S is finite: retain its prescribed values and enumerate all natural-number outputs on the infinite remaining input set. Since g and h have the same codomain and agree on both pins,

$$
p\text{ has the same truth at }g\text{ and }h,
\qquad
q\text{ has the same truth at }g\text{ and }h.
$$

Thus g still distinguishes p,q, and §3 makes every g_σ onto.

The criterion of §2 therefore applies for every finite Δ. For each pair and list it constructs an admitted full Good_Δ observer with the required disagreement. Consequently **full typed OS holds at W₀**.

The distinguishing arrow can work for all finite lists; the normalized observer may depend on Δ. No infinitary qualification or simultaneous choice of a family of observers is asserted. The raw observer was obtained only from extensional fullness, and its unprescribed future behavior is handled by the guard.

As a separate consistency check, the existing record already gives BF at W₀, and the proved database result [BF implies Functionality](../../source/topics/classicism/results/barcan-r-implies-functionality-r.yaml) gives the Functionality used for typed lifting. The new OS argument does not presuppose the conclusion it proves.

## 5. Necessary BF fails at the same point

The singleton W₁ is accessible from W₀ by c. At W₁ let x be its only individual and set F(y):=(y=x). Since every current y equals x, each current F(y) is Top, so
$\forall y^e\,\Box F(y)$
is true there. But after any arrow i_n:W₁→W₀, the transported predicate is equality to n, which is not true of every natural number. Thus the proposition ∀y F(y) is not Top at W₁, and BF_e fails there. Therefore necessary BF_e, and hence the necessary all-type BF schema, fails at W₀.

The model record also establishes failure of necessary BF_t. Its witness at W₁ uses the admitted profile that is true at the identity, and at an arrow h exactly of the propositions in the image of h_t. Every current proposition necessarily satisfies this profile, but some proposition at the future ℕ object lies outside that transport image. The record gives the explicit image calculation and finite pin for this witness. This stronger recorded failure is retained without changing its attribution.

The same individual witness directly refutes Functionality at e,t at W₁. Compare G:=λy.(y=x) with H:=λy.Top. At the only current individual their values are the same proposition Top. The two predicates are nevertheless distinct: after i_n, their truth values differ at any individual m≠n. Thus current pointwise identity does not identify G,H at W₁. Necessary Functionality at e,t therefore fails at W₀, and so does the necessary all-type Functionality schema.

The established profile is therefore

$$
\boxed{\mathrm C+\mathrm{OS}+\mathrm{BF}
       +\neg\Box\mathrm{BF}_e+\neg\Box\mathrm{BF}_t
       +\neg\Box\mathrm{Fun}_{e,t}.}
$$

In particular ordinary OS does not imply necessary OS, necessary BF, necessary BF_t, or necessary Functionality. The new separations concern necessary BF and Functionality; failure of necessary OS already had other witnesses.

## 6. Evidence and limits

A proved-only `scripts.pmap.load_topic` / `Engine` check, with empty background and this single recorded model, confirms BF, Functionality, failure of necessary BF, failure of necessary BF_t, and no model conflict. The BF-to-Functionality derivation is `barcan-r-implies-functionality-r`. The engine does not establish the new OS verdict: that is the ordinary argument in §§2–4.

The decisive combination is extensional fullness, arrows with onto transports that distinguish each proposition pair, and C's unconditional finite guard. Persistent qualification alone was not assumed to make separation persistent. Full action models and the earlier root truth-profile extension are not substituted for this finitely pinned model; their stronger transport properties would obscure the contingent-Barcan behavior.

 The direct source for the new criterion and OS verdict is `misc`, OpenAI Codex, prompted by Daniel Kodsi, 24 October 2026, §§2–4, unpaginated. The original model, C soundness and Barcan failures retain the source locators and verification history in their linked records.
