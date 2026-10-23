# Strong Possibility: products, reduced products, and minimal identity algebras

22 October 2026. Original research by OpenAI Codex subagent, ordinary mathematics. No human check or formal verification is claimed. No main database edits. Direct source of the results below: this note, §§1–4 (misc). Framework and notation: Bacon–Dorr, *Classicism*, draft 16 May 2023, §§1.1–1.3; Strong Possibility §2.6, p. 42. The exact type system is relational: arrows have non-individual codomain. The identity-former is included among the algebra's logical term operations.

## 1. A universal connectedness law of C

Write `eq(p,q)` for the proposition denoted by the object-language identity `p=q`, distinguishing it from literal equality in a semantic algebra. Every pointed model of C satisfies

    ∀p [ (eq(p,top)=p ∧ eq(p,bottom)=¬p)
          → (p=top ∨ p=bottom) ].                       (Conn)

All the displayed equalities, including the conclusion, are object-language identities, and the whole formula is a universal Boolean combination of identities of the permitted kind. Indeed, fix p satisfying its antecedent. By classical bivalence, either p is true or ¬p is true. In the first case eq(p,top)=p and substitution imply that eq(p,top) is true, so p literally equals top. In the second case eq(p,bottom)=¬p similarly implies that p literally equals bottom. This proof uses only H with identity and classical truth; it does not use Maximalism.

C also proves eq(top,top)=top, eq(bottom,bottom)=top, eq(top,bottom)=bottom, and eq(bottom,top)=bottom. These are identities, not just actual equivalences: the corresponding formula equivalences are H-theorems, so Logical Equivalence applies legitimately.

## 2. Ordinary products cannot be pointed C models

Let A and D be the complete term-operation reducts of any two nondegenerate C models. Form their sorted direct product with componentwise interpretation of every term operation, including eq. Its proposition domain contains r=(top_A,bottom_D). Then

    eq(r,top)=r,       eq(r,bottom)=¬r,

by the four identities at the end of §1. But r is literally neither top nor bottom. Thus (Conn) fails in this algebra. Consequently there is no classical truth predicate on the product which makes it a pointed C model while retaining its coordinatewise operations and literal identity.

This is stronger than the familiar warning that arbitrary universal disjunctions are not preserved by products. The direct product of two C-model algebras already violates a universal identity-fragment theorem of C itself. Adding a designated truth ultrafilter cannot repair the problem without changing either the algebra or its equality interpretation.

An arbitrary subproduct need not contain r. Therefore the theorem does not exclude suitably restricted subproducts. It does require every such subproduct intended as a C algebra to omit all nontrivial two-valued coordinate selectors.

## 3. A sharp reduced-product obstruction

Let (A_i)_(i∈I) be nondegenerate C-model term algebras, and let F be a proper filter on I. Form the ordinary sorted reduced product modulo F, with coordinatewise logical operations. If that reduced product admits a pointed C expansion retaining literal identity, then F is an ultrafilter.

Proof. Suppose F is not an ultrafilter. Choose S⊆I with neither S nor I\S in F. Let r_i=top_i for i∈S and r_i=bottom_i otherwise. In the quotient, r differs from top because S∉F, and differs from bottom because I\S∉F. Coordinatewise computation still gives eq(r,top)=r and eq(r,bottom)=¬r. This contradicts (Conn). Therefore every S or its complement belongs to F, which is exactly ultrafilterhood. □

For an ultrafilter U, the usual many-sorted first-order ultraproduct of the full pointed Henkin structures does preserve C and pure Max: include truth, application, and the logical operations in the structures, and apply the first-order ultraproduct theorem to every instance of the schemata. The quotient equality agrees with the truth of coordinatewise eq precisely because U is an ultrafilter. This positive observation assumes the actual Henkin structures are being ultraproducted, rather than merely arbitrary algebras known to satisfy some identities.

Thus a filter-based product cannot average incompatible universal alternatives into a new minimal C structure while postponing the choice of truth: it must already make an ultrafilter choice.

## 4. What the product obstruction does and does not settle

Let M=Max(C). A supplied reduction identifies pure SP-models with M-models satisfying every individually M-consistent universal Boolean identity sentence. Equivalently, the existential Boolean identity sentences true in such a model are exactly those entailed by M. The product lemmas do not refute the existence of that model.

There is a common pointed pure-term algebra B: its domains consist of pure terms T(a) with one distinguished individual parameter, identified exactly when C(a) proves their equality. Unary Possibility+ ensures that the natural map from B into any M-model, obtained by choosing one actual individual, is an embedding of all term operations. Therefore B satisfies every individually M-consistent universal Boolean identity sentence: choose an M-model satisfying that sentence and restrict to B. This uses downward preservation under embeddings, not closure of Henkin models under arbitrary subalgebras.

A potentially weaker target than making B itself a pointed Henkin model is to find a pointed Henkin expansion of some algebra B* elementarily equivalent to B (for the full term-operation language). Such B* may contain new relational witnesses, while its existential identity theory remains that of B. If the expansion satisfies M, it is an SP-model by the supplied reduction. Saturated elementary extensions or ultrapowers offer room for witnesses that B itself lacks.

The remaining obligation is real: consistency of the elementary algebraic theory of B together with the classical truth and Henkin quantifier clauses and M has not been proved. Resplendency cannot be invoked without first establishing that relative expansion consistency. An ultraproduct of already available M-models gives the desired minimal theory only if the needed finite collections of universal constraints are already jointly realizable, which is precisely the unresolved disjunction-property problem.

## 5. New consequence: no strong worlds at any relational type

Let τ be any relational type, including t. Recall

    SWorld_τ(w) := w≠bottom_τ ∧ □∀Y^τ (w≤_τY ∨ w≤_τ¬Y).

**Theorem.** Pure Strong Possibility entails

    ∀w^τ ¬SWorld_τ(w)                               (NSW_τ)

for every relational τ. In particular its forced atoms A_n=F∧E_n are all weak worlds and none is strong.

### 5.1 The single type-t Strong Possibility instance

Put D_t(w):=∀p^t(w≤p∨w≤¬p). The sentence

    U_t := ∀w^t [w=bottom ∨ D_t(w)≠top]

is a closed pure universal Boolean combination of typed term identities: D_t(w) is a term of type t, even though its internal syntax contains quantifiers. It is exactly NSW_t after expanding □D as D=top.

The recorded model `coalesced-pinned-substitutions-root` satisfies signature Maximalism and propositional Atomlessness. Its pure reduct therefore satisfies pure Maximalism and U_t, because every strong world is a weak world by T, and Atomlessness forbids all weak worlds. Consequently Max(C)+U_t is consistent. Strong Possibility supplies ◇_≠U_t; universal-identity reflection gives U_t. Only this one SP instance is needed for all the types below.

Source caveat: the cited record has a proved atomlessness argument attributed to Claude Opus 5.5 at Cian Dorr's direction, dated 19 October 2026; its note expressly says the model verification has not been checked by a second reader. This theorem uses that recorded construction as given and does not upgrade its checking status. Exact source entry: `topics/classicism/models/coalesced-pinned-substitutions-root.yaml`, argument `atomlessness`, and matching write-up. The general background is Classicism Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74; Appendix E, Definition E.2, pp. 80–83 (16 May 2023 pagination).

### 5.2 Projection of a strong relational world to a strong proposition

Write τ=σ_1…σ_k t and put

    π(W) := ∃x_1^σ1…x_k^σk W[x_1,…,x_k],
    K(p) := λx_1^σ1…x_k^σk.p.

For k=0 both maps are the identity. C proves the adjunction

    W≤_τK(p)  ↔  π(W)≤_t p,                         (Adj)

because the left side is equivalent to □∀x̄(W[x̄]→p), and the right side to □((∃x̄W[x̄])→p); the enclosed formulas are H-equivalent. This is a theorem of the fixed C, so its necessitation is licensed. In particular

    W=bottom_τ  ↔  π(W)=bottom_t.                    (Zero)

Now suppose SWorld_τ(W). By its boxed settlement condition, instantiate Y at K(p), at every point and for arbitrary p. Since ¬_τK(p)=K(¬p) is a C identity, this yields

    □∀p (W≤_τK(p) ∨ W≤_τK(¬p)).

Use the necessitated theorem (Adj) to obtain

    □∀p (π(W)≤p ∨ π(W)≤¬p).

By (Zero), π(W) is nonbottom. Hence SWorld_t(π(W)). We have proved in C, with no BF, Actuality, choice, or optional extensionality,

    SWorld_τ(W) → SWorld_t(π(W)).

Taking contrapositives and universally closing gives U_t→NSW_τ. Together with §5.1, this proves the theorem for every relational type.

### 5.3 Scope and strictness

The conclusion forbids arbitrary actual strong-world entities, not merely pure-named strong worlds. It does not say there are no weak worlds: the profile-root construction and universal reflection force Atom_t(A_n) under pure SP for every positive external integer n. Therefore, conditionally on SP consistency, infinitely many distinct weak worlds exist and no strong world exists.

The prohibition is not a consequence of pure Max alone. In the profile-root construction of `profile-root-construction-20261022.md` §§1–3, the proposition with actual coordinate true and bottom profile is a true strong world: at the root it is the root-only atom and settles every root proposition; along every nonidentity arrow it is bottom and settles every proposition trivially. That model satisfies pure Max. Thus the new conclusion is a strict strengthening over pure Max, assuming the stated two model constructions.

## 6. Stronger consequence: simultaneous possible atomlessness of all finite current diagrams

This strengthens §5. Its key idea was communicated independently by the parent research agent; the proof below gives a shorter route from the single Strong Possibility instance for propositional Atomlessness.

For a relational type τ define

    AL_τ(W) := W≠bottom_τ ∧
      ∀Y^τ [(Y≠bottom_τ ∧ Y≤W) →
        ∃Z^τ (Z≠bottom_τ ∧ Z≤Y ∧ Z≠Y)].

This says the nonzero interval below W is atomless. Let AL_t^global be propositional Atomlessness, i.e. every nonzero propositional interval is atomless. Put D=◇_≠ and B=□_≠.

**Theorem.** Pure SP entails D AL_t^global. Furthermore, for every fixed finite tuple of relational types τ_1,…,τ_m, pure SP proves

    ∀W_1…W_m [ (⋀i W_i≠bottom_(τ_i)) →
      D (AL_t^global ∧ ⋀i AL_(τ_i)(W_i)) ].          (SimAL)

The empty-tuple case is the initial D AL_t^global assertion. These are statements in the original finitary system. No single target for infinitely many current parameters is claimed.

### 6.1 Propositional atomlessness implies atomlessness at every relational type

Use π and K from §5.2. In addition to the nonzero equivalence (Zero), C proves

    π(W∧_τK(p)) = π(W)∧p.                          (Meet)

This follows by Logical Equivalence from the H-equivalence between ∃x̄(W[x̄]∧p) and (∃x̄W[x̄])∧p. No BF occurs.

Suppose AL_t^global and Y≠bottom_τ. Then q=π(Y) is nonbottom. By propositional atomlessness choose a nonzero proper part r≤q. Since r is proper, q∧¬r is nonzero. Let Z=Y∧K(r). By (Meet), π(Z)=q∧r=r, so Z is nonbottom. Also π(Y∧K(¬r))=q∧¬r is nonbottom. The latter relation is disjoint from Z and below Y, so Z≠Y. Thus Z is a nonzero proper part of Y. We have proved C's theorem

    AL_t^global → ∀W^τ (W≠bottom_τ → AL_τ(W)).      (AllTypes)

This does not infer arbitrary external subsets or use full semantics; every splitter is obtained by the allowed lambda and Boolean operations from a propositional splitter.

### 6.2 Transporting each finite current diagram

Every identity and every disequality is B-persistent in C. Equality persistence follows from NI and □≤B. For s≠t, NI gives the theorem ◇(s≠t)→s≠t; its boxed instance and the true witness q:=(s≠t) in the definition of B prove (s≠t)→B(s≠t). Finite Boolean combinations are B-persistent by classical cases and normality of B. In particular, with R:=⋀i(W_i≠bottom_(τ_i)), C proves R→BR.

By the recorded atomless-Max model, AL_t^global is Max-consistent. Thus SP gives D AL_t^global. Normal modal reasoning for B and its dual gives

    BR ∧ D AL_t^global → D(R∧AL_t^global).

The fixed-C theorem (AllTypes), necessitated legitimately, converts the right side into the desired D(AL_t^global∧⋀iAL_(τ_i)(W_i)). This proves (SimAL).

More generally, for any finite Boolean combination θ(c̄) of typed identities, and any closed pure Max-consistent Q, pure SP proves

    θ(c̄) → D(Q∧θ(c̄)).                            (FiniteDiagram)

This is a useful parameter-sensitive consequence of a pure schema: parameters occur in the preservation lemma, not in the schema's metalinguistic side condition. It does not replace the reference Max(C) by a stronger theory.

### 6.3 Consequences and limits

Apply (SimAL) to the forced distinct weak atoms A_1,…,A_m. They can simultaneously remain nonzero and acquire atomless intervals at a distinctness-preserving possibility. Thus their actual weak atomicity cannot be read as necessary atomicity; newly admitted entities can split the transported atoms while all finite current identity information is preserved.

Atomlessness below a nonzero entity implies finite disjoint splitting of any prescribed standard size, by iterating the nonzero-proper-part property finitely many times. Consequently, every finite tuple of currently nonzero relational entities has a common distinctness-preserving possibility at which each has arbitrarily large prescribed finite splittings. The stronger statement (SimAL), which makes each interval entirely atomless at that possibility, is what is actually proved.

There is no contradiction with actual weak atomicity. Weak atomicity is universal in all current entities; it need not persist when the domains gain new entities. Strong atomicity would persist its settlement condition and is therefore excluded, as in §5.

## 7. Vicinity audit: the boxed and unboxed statements remain distinct

The parent agent requested checking whether the preceding method proves SP→¬Vicinity. It does not presently establish that implication.

Vicinity is equivalent in C to the existence of a least nonzero possibility-fixed proposition:

    ∃r [r≠bottom ∧ r=◇r ∧
      ∀q(q≠bottom → r≤◇q)].                        (LV)

For the forward direction let v witness the original Vicinity and take r=◇v. A nonzero q makes ◇q actually true; Vicinity applied to that truth, together with ◇◇q=◇q, yields v≤◇q and hence ◇v≤◇q. Conversely, r=◇r and r≠bottom imply r is actually true, and each true q is nonzero, so r witnesses the original formulation. At such an actual witness r,

    Bp ↔ r≤p,       Dp ↔ r∧p≠bottom.

For Bp→r≤p, a true witnessing q gives r≤◇q and ◇q≤p. Conversely r itself is true and possibility-fixed, so r≤p supplies a witness in B's definition. The dual follows by Boolean algebra.

The obstacle is the unboxed universal clause in (LV). D preserves the witness's disequality r≠bottom and identity r=◇r, but need not preserve its minimality among ALL propositions. New propositions at a target can violate minimality, just as they can split an old weak atom. It is not valid to replace that clause by its box or use the existential-identity disjunction property directly on (LV).

By contrast, define StrongVicinity as the existence of r with r≠bottom, r=◇r and

    □∀q(q≠bottom → r≤◇q).

Its negation IS a universal Boolean identity sentence, and the recorded Max+¬Vicinity model satisfies it. Thus UMax excludes StrongVicinity. Equivalently, SP gives D¬Vicinity directly; any strong witness would remain nonzero, possibility-fixed and minimal at such a target, contradicting ¬Vicinity. No promotion of actual Vicinity to StrongVicinity has been proved.

The source's 5-necessity formulation of Vicinity supplies a true proposition entailing every currently 5-necessary truth, with a refined witness itself 5-necessary (Sun, argument of 19 October 2026, as recorded in the `vicinity` principle). Its displayed minimality still quantifies over the current domain. Neither the recorded argument nor the work here justifies boxing that minimality in the original □ modality. Accordingly SP→¬Vicinity remains unresolved in this note.

## 8. Finite relational spectra over the finite extensional cells

This is another original consequence of the profile-root construction, using the exact relational type system. It is more explicit than the propositional atom case.

Fix external integers n≥1 and k≥0. Let τ=e^k t, let A_n=F∧E_n, and choose an individual parameter a. Let Π_(n,k) be the finite set of partitions of the labeled positions {0,1,…,k} into at most n nonempty blocks. Position 0 represents a, and position i represents x_i. For π∈Π_(n,k), let δ_π(a,x_1,…,x_k) assert precisely the equalities and disequalities described by that partition, and define

    C_π(a):=λx_1…x_k. A_n ∧ δ_π(a,x_1,…,x_k).

For k=0 the unique cell is A_n itself. Write A_n^τ:=λx_1…x_k.A_n. For each subset S⊆Π_(n,k), let T_S(a) be the finite Boolean join of its C_π(a), with empty join bottom_τ.

**Theorem.** Pure SP entails, for every a,

    ∀X^τ ⋁_(S⊆Π_(n,k)) [ A_n^τ∧_τX = T_S(a) ].    (Spectrum)

Each C_π(a) is nonzero, the cells are pairwise disjoint, and their join is A_n^τ. Consequently the Boolean interval [bottom_τ,A_n^τ] has exactly 2^K elements and exactly K atoms, where

    K=|Π_(n,k)|=Σ_(j=1)^min(n,k+1) S(k+1,j)

and S(k+1,j) denotes the ordinary Stirling number of the second kind. The counting is external finite counting, not an identification with the map's impredicative Frege cardinalities.

### 8.1 Model verification of the spectrum sentence

Use the singleton profile root of `profile-root-construction-20261022.md` §§1–4. An actual X of type e^k t has a profile T(z) for a pure term with one free individual variable. At every A_n-world, the local structure is the full n-individual extensional hierarchy. Every permutation of individuals fixing the marked z-value is an automorphism. The orbits of k-tuples under that stabilizer are exactly their equality partitions relative to the marked value, namely Π_(n,k).

It follows that T(z) is constant on each such orbit. The set of orbits on which it is true is the same in every pointed A_n-world: these pointed full finite structures are isomorphic. Thus the profile of A_n^τ∧X equals the profile of T_S(z) for some fixed S⊆Π_(n,k). Their actual extensions are both empty because A_n is actually false at this root. The entities are therefore equal as profile/root-extension pairs. Since the root has one actual individual, the universally closed sentence ∀a∀X(Spectrum's matrix) holds there.

That sentence is a finite universal Boolean combination of identities, with no nonlogical constant: a is universally bound. It is Max-consistent by the construction. Universal-identity reflection plus SP proves it.

### 8.2 Nonzero cells and the exact Boolean interval

Distinct cells are disjoint and their join is A_n^τ by ordinary equality case analysis at an n-individual world; the relevant identities follow from the necessary universal closure of those implications in C.

For each π with at most n blocks, the pure one-individual-variable formula

    A_n ∧ ∃x_1…x_k δ_π(a,x_1,…,x_k)

is C-consistent, witnessed by the full n-individual extensional model with a chosen marked individual. Unary Possibility+ for pure Max makes its possibility true for every actual a. Equivalently C_π(a)≠bottom_τ. Thus nonzero cells already follow from Max; SP adds that no further splitting by current relations is possible.

If Y≤C_π(a), then Y=A_n^τ∧Y. Apply (Spectrum): Y is some finite union of cells. Pairwise disjointness and nonzeroness make Y≤C_π possible only for the empty union or the singleton union {π}. Hence C_π is an atom. Conversely any nonzero union with at least two cells has a proper nonzero cell below it. Every union corresponds to a different subset of Π because the cells are disjoint and nonzero. This proves the exact counts.

### 8.3 Small cases

* k=0: K=1 for every n; the result is Atom_t(A_n).
* k=1, n=1: K=1; A_1-localized unary properties have two values.
* k=1, n≥2: K=2; the atoms are `A_n∧x=a` and `A_n∧x≠a`, and there are four localized unary-property values.
* k=2, n=2: K=4; there are sixteen localized binary-relation values.
* k=2, n≥3: K=5; there are thirty-two localized binary-relation values, corresponding to the five equality patterns of a,x,y.

By §6, these currently finite intervals can simultaneously become nonzero and atomless under distinctness-preserving possibility. Their finite actual spectra therefore provide no necessary finite-domain conclusion and no contradiction with the atomless-target requirement.

## 9. Exact finite localization at every relational type

This extends §8 beyond individual-input relations. Fix n≥1. Let D^n be the full extensional relational hierarchy over the labeled individual set {1,…,n}. Thus D_e^n={1,…,n}, D_t^n={0,1}, and D_(στ)^n is the full function set from D_σ^n to D_τ^n for each admitted arrow type. Let H_n be the permutations of {1,…,n} fixing 1. They act on all higher domains by the usual conjugate action on functions.

For a relational type τ=α_1…α_k t, let

    Ω_(n,τ) := (D_(α_1)^n × … × D_(α_k)^n) / H_n,
    o_(n,τ) := |Ω_(n,τ)|.

The empty product for τ=t has one member. A τ-entity is fixed by H_n exactly when its truth set is a union of these orbits. Hence the fixed entities form a finite Boolean algebra with o_(n,τ) atoms and 2^o_(n,τ) elements.

### 9.1 Finite hierarchy automorphisms are exactly individual permutations

Any individual permutation extends uniquely through the hierarchy, fixes the two truth values, and acts on a function f:σ→ρ by

    (g·f)(g·x)=g·(f(x)).

This preserves application, the Boolean operations, identity, abstraction and quantifiers; quantified domains are carried bijectively to themselves. Conversely an automorphism's action on e is an individual permutation, and its action on t fixes bottom and top. Once its actions on σ and ρ are known, the displayed application identity determines its action on every f:σ→ρ, because all inputs are covered. Induction on type complexity gives uniqueness at every type. Thus there are no additional higher-type automorphisms independent of the individual action.

### 9.2 Every invariant entity has a pure term with the marked individual as sole parameter

First name every entity using a complete labeled enumeration x_1,…,x_n of the individuals. Inductively construct a pure term N_d(x_1,…,x_n) for every d∈D_σ^n. At e use x_i; at t use bottom and top. At σ→ρ, where ρ is relational, take the finite table

    N_f(x̄) := λy^σ.
      ⋁_(d∈D_σ^n) [ K_ρ(y=N_d(x̄)) ∧_ρ N_(f(d))(x̄) ],

where K_ρ lifts a proposition constantly to the relational output type ρ. All types used are admitted. In a full finite extensional world, each equality test is top exactly at its named input and bottom otherwise. The finite table therefore denotes f. This is an induction on type complexity: both input and output types are smaller than the function type.

Now fix an H_n-invariant d∈D_τ^n. Write τ=α_1…α_k t, let Enum_n(a,x_2,…,x_n) say these n individuals are pairwise distinct and exhaust e, and define

    R_d(a) := λy_1…y_k.
      ∃x_2…x_n [ Enum_n(a,x_2,…,x_n) ∧
        N_d(a,x_2,…,x_n)[y_1,…,y_k] ].

For n=1 the existential tuple is empty. At an A_n-world with a marked individual, every admissible enumeration with first entry a differs from any other by a permutation fixing that individual. Invariance of d therefore makes every enumeration give the same τ-entity. At least one enumeration exists. Consequently R_d(a) denotes exactly d, under the identification sending label 1 to a. It is a pure term with a as its only possible free variable. This proves definability, not merely invariance of already definable entities.

### 9.3 The SP spectrum theorem

For every actual individual a, pure SP makes the Boolean interval below A_n^τ isomorphic to the fixed algebra (D_τ^n)^(H_n). Concretely, for the finite list of invariant entities d,

    ∀a^e∀X^τ ⋁_(d∈(D_τ^n)^(H_n))
      [ A_n^τ∧_τX = A_n^τ∧_τR_d(a) ].              (AllTypeSpectrum)

The proof uses the profile root. Any profile term T(a) takes an invariant value at the pointed full finite A_n-structure, and §9.2 names that value. Thus its localization agrees with the corresponding localized R_d at every object where A_n is true and every argument tuple. This implies identity of the localized intensions: equivalently, the fixed-C modalized extensionality theorem turns the necessary universal pointwise equivalence into identity. At arbitrary non-Fregean component objects A_n may be false without being bottom, so one must use this all-future pointwise argument; mere equality of actual extensions at those component objects would be insufficient.

The profile-root actual extensions are empty since A_n is false there. Hence (AllTypeSpectrum) holds at that Max root. It is a finite universal Boolean identity sentence, so SP reflects it.

Distinct invariant d,e remain distinct after localization in every Max model. In the full pointed n-individual model, some argument tuple separates R_d(a) and R_e(a). Therefore the pure one-individual-variable sentence

    A_n ∧ ∃ȳ [ R_d(a)[ȳ] ↔ ¬R_e(a)[ȳ] ]

is C-consistent. Unary Possibility+ makes its possibility true at every actual a in a Max model. This is exactly nonidentity of the two localized relations. Similarly each orbit's characteristic entity gives a nonzero localized relation. Finite disjoint orbit decomposition and (AllTypeSpectrum) then identify the exact Boolean algebra and prove the atom count o_(n,τ).

### 9.4 Further examples

For τ=et, H_n has one orbit on e if n=1 and two if n≥2. Thus the localized Boolean algebra has 2 values for n=1 and 4 values for n≥2.

For τ=(et)t, its inputs are subsets of the n individuals. A subset's H_n-orbit is determined exactly by (i) whether it contains the marked individual and (ii) how many of the remaining n−1 individuals it contains. There are 2n such orbits. Therefore pure SP forces the A_n-localized type-(et)t Boolean interval to have exactly 2n atoms and exactly 2^(2n) elements. The atoms are represented by the pure predicates saying, under A_n, that a property contains or omits a and contains exactly j other individuals, for j=0,…,n−1.

For τ=tt, the two proposition inputs are fixed by every H_n, giving two atoms and four localized operation values for every n.

These counts concern the current localized intervals under SP. They do not assert finite global type domains, necessary finite intervals, or fullness of the current higher-order structure. Section 6 forces the same nonzero tops to have atomless intervals at suitable distinctness-preserving possibilities.

## 10. Uniform Fregean symmetry beyond the finite cells

This section does not assume the individual domain is finite. It uses finite individual permutations, which are definable type by type even in a general Fregean Henkin model. No closure under arbitrary infinite permutations is claimed.

### 10.1 Definable individual swaps preserve every Henkin type domain

At a world satisfying the Fregean Axiom F, the proposition domain consists of bottom and top, and every relational type is extensional. Fix individuals b,c. Let s_e interchange b and c and fix every other individual; let s_t be the identity. Inductively, for every admitted arrow type σρ, define the semantic action

    s_(σρ)(X)(y) = s_ρ(X(s_σ(y))).

When σ is relational, this is represented by the lambda term obtained from the already constructed terms for s_σ and s_ρ. When σ=e, no ee term is used: replace X(s_e(y)) by the pointwise Boolean conditional which takes X(c) if y=b, X(b) if y=c, and X(y) otherwise. The output ρ is relational, so those Boolean conditionals are admitted. If b=c take the identity; the displayed conditional gives the identity in that case too.

By induction these transformations are involutions on the actual type domains. Their images stay in the domains by Henkin term closure, and they have inverses because applying the involution twice is pointwise identical to the original entity; Fregean extensionality converts that into entity identity. Thus each s_σ is a bijection, even when its domain is infinite and not full.

The actions preserve application by their defining conjugacy formula. They preserve identity because they are bijections; Boolean operations because s_t fixes bottom and top; and quantifiers because each quantified domain is permuted bijectively. Induction on syntax therefore proves equivariance of every pure term. This verifies that the typewise action is an automorphism of the pointed typed structure when all named/parameter individuals are fixed.

Every finite individual permutation is a finite composite of such swaps, hence similarly extends. In particular, if a is distinguished, the finite permutations fixing a act transitively on the tuples with any given equality pattern relative to a, even in an infinite individual domain: a finite partial bijection matching the finitely many displayed individuals extends to a finite permutation.

### 10.2 A uniform localized orbit formula

Fix k≥0 and let Π_k be all partitions of {0,…,k}, with no cardinality bound. For a relation X:e^k t and an individual a put

    b_π(X,a) := ∃y_1…y_k [δ_π(a,ȳ) ∧ X[ȳ]],
    O_π^F(a) := λx_1…x_k. F ∧ δ_π(a,x̄).

Then pure SP entails

    ∀a∀X [ F^(e^k t) ∧ X =
      ⋁_(π∈Π_k) (O_π^F(a) ∧ K(b_π(X,a))) ].       (F-Sym)

Here K lifts the coefficient proposition constantly to the relation type. If a pattern is unrealizable because the individual domain is too small, its orbit relation is bottom at that Fregean world, so no exception is needed.

Proof of Max-consistency: in the singleton profile root, X has a profile T(a) with no free variables other than the distinguished individual. At every Fregean target, §10.1 makes T(a) invariant under finite permutations fixing a, hence constant on each realizable equality-pattern orbit. The coefficient b_π records exactly whether that orbit is included. Thus the two localized sides agree pointwise at every Fregean target and every tuple. As in §9.3, all-future pointwise equivalence yields identity of the localized profiles; their root extensions are empty because F is false there. The universally closed identity (F-Sym) holds at that Max root. Universal-identity reflection proves it under SP.

For k=1 this says explicitly

    F∧X = F∧λx.[(x=a∧Xa) ∨
      (x≠a∧∃y(y≠a∧Xy))].

Thus every currently available unary property, when transported to a Fregean world, is either constant on the individuals other than the transported a or has no such individuals to distinguish. The truth values on a and on its complement may vary between worlds. This is why it is a uniform two-coefficient decomposition, not an unconditional four-element bound for the entire F-localized Boolean interval. Restricting to A_n and using its atomicity recovers the four-value bound for n≥2.

### 10.3 All relational types: invariance under future unmarked swaps

For any fixed relational τ, the term Sw_τ(b,c,X) implementing §10.1 exists with relational output. Pure SP also forces the universal identity-fragment assertion

    ∀a∀X^τ [ F ≤ ∀b^e c^e
      ((b≠a∧c≠a) → Sw_τ(b,c,X)=X) ].              (Swap-Inv)

The inequality F≤Q is an identity of proposition terms, so only the outer a,X quantifiers are relevant to the universal-identity classification. The proof again uses the profile root: at each Fregean target a pure profile T(a) is fixed by every individual swap fixing a, and the resulting implication holds at all further targets. This is not merely the vacuous actual statement about swaps in SP's singleton current individual domain; the displayed ≤ places the unmarked swaps inside necessary pointwise evaluation.

Neither (F-Sym) nor (Swap-Inv) asserts arbitrary infinite-permutation closure of Henkin domains. Both are proved using finite swaps only. Nor do they constrain newly existing relations at a target in the same way: the quantified X is an entity from the original point, while the inner b,c can range over additional individuals at the target.

## 11. Pointed versus unpointed completeness over F

For every pure formula P(x) with one free individual variable and no other free variables, C proves

    F → (∃x P(x) ↔ ∀x P(x)).                       (Hom)

At any Fregean Henkin world, the swap automorphism of §10.1 can carry any individual to any other. Pure formula truth is invariant under it, so all individuals agree on P. Domains are nonempty, proving the equivalence. Equivalently one can perform the fixed-type swap induction syntactically; the semantic argument uses the same Henkin completeness assumed in the profile-root construction.

Consequently every complete pure theory T extending C+F has exactly one consistent completion after adding one individual constant a. For each sentence P(a), replace a by x; by (Hom), its truth is equivalent over T to the pure sentence ∃xP(x), which T decides. Consistency is supplied by interpreting a as any individual of a T-model.

Therefore, for every closed pure A with C⊢A→F, the space of complete C(a)+A theories is naturally in bijection with the space of complete pure C+A theories, by restriction and the unique pointed expansion. In the parent's finite-rank theorem (`sp-finite-profile-rank-20261022.md`), the pointed completion count may therefore be replaced by the unpointed count for Fregean A. This replacement is not valid for arbitrary A; the general pointedness caveat remains necessary.

## 12. Restrictions on current relational structures at Fregean targets

These are consequences of (Swap-Inv), stated to make its strength concrete. Quantification over R below is at the original point. The structural tests inside □ concern its transported relation and the target individual domain. No inadmissible individual-output function type is used; functions are represented by total single-valued binary relations.

### 12.1 Orders have at most two individuals

Pure SP entails: for every current binary relation R, necessarily, if F holds and R is a strict linear order of all individuals, there are at most two individuals.

At any such target let a be the transported unique original individual. If there are at least three individuals, choose distinct b,c different from a. The swap b↔c fixes R by (Swap-Inv). Hence R(b,c) iff R(c,b), contradicting strict totality and asymmetry. This proves the claim. It does not say no Fregean target has an order: a target may have a new order absent from the original domain.

### 12.2 Functional injections cannot witness individual infinity

Pure SP entails: for every current binary relation R, necessarily, if F holds and R is the graph of a total injective map from individuals to individuals, that map is surjective.

If the target domain has at most three individuals, ordinary finite pigeonhole suffices. Otherwise let f denote the external map uniquely described by R and let a be the transported original individual. Equivariance under all finite swaps fixing a implies f(a)=a: any other output could be moved while fixing a. If x≠a, injectivity gives f(x)≠a. If f(x)≠x, choose z outside {a,x,f(x)}, possible because there are at least four individuals. Swapping f(x) and z fixes a and x but changes f(x), contradicting equivariance. Thus f(x)=x for every x, so f is the identity and in particular surjective.

The argument for at least four individuals actually shows identity, not merely surjectivity. At two or three individuals a nonidentity equivariant permutation may exist; these finite cases were kept separate deliberately. The boxed conclusion does not require BF: it is evaluated at arbitrary targets after transporting the already quantified R and a.

### 12.3 Group graphs have at most four individuals

Pure SP entails: for every current ternary relation G, necessarily, if F holds and G is the graph of a group operation on all individuals, there are at most four individuals.

Suppose a target has at least five individuals. Each finite permutation fixing the transported a is an automorphism of G. The group's identity is uniquely characterized and therefore fixed by all such permutations; the only commonly fixed individual is a, so a is the group identity. Choose x≠a and choose y outside {a,x,x^(-1)}. Then z=xy is distinct from a,x,y. Choose w outside {a,x,y,z}. The transposition z↔w fixes a,x,y and must preserve G, but it moves the unique product of x and y. Contradiction.

For four individuals, the only possible group is the Klein four group: the cyclic group of order four has a uniquely characterized nonidentity element of order two, which cannot be fixed by every permutation of the three nonidentity elements. Orders one, two and three give the familiar cyclic groups. These last classifications are ordinary finite group calculations, not additional modal assumptions.

Again this constrains current G. Pure Max still requires possibilities with ordinary large groups, and those groups must be represented by relations newly available there. The result is consistent with the earlier BF and Functionality failures and does not itself refute SP.

## 13. Stronger locality: necessary ND at the individual type

Define the single closed pure sentence

    G := □ND_e := □∀x^e y^e (x≠y → □(x≠y)).

This is only the individual-type instance, not the whole all-type C5 preset. The Fregean Axiom implies G, as recorded by the Fregean-to-boxed-ND argument. The symmetry conclusions below therefore strengthen the F-local ones.

### 13.1 Natural swaps when future individual transport is injective

At an action-model point satisfying G, every arrow between worlds reachable from that point has an injective individual transport: ND_e at its source prevents any distinct individuals being identified by the arrow. Fix two individuals b,c at the point. At each future arrow h, swap h(b) and h(c), fixing all other individuals. This family commutes with every further transport k. If an individual is one of h(b),h(c), this is immediate. If it is neither, injectivity of k ensures that its image is neither k h(b) nor k h(c), proving the remaining case.

Thus the swaps form a natural involution of the individual domains on the future/coslice category. They are not merely unrelated permutations of each world's current set. This distinction is essential for intensional lambda abstraction.

The typewise lift is the same recursive term Sw_τ(b,c,X) used in §10.1: identity at t, conjugation at relational inputs, and the three-way Boolean conditional at individual inputs. Because individual equality and disequality are necessary at every future point, each conditional selects its corresponding branch throughout subsequent transports. The lifted maps are natural involutions at all types; their values belong to all Henkin domains by term closure. Induction on type and term interpretation gives preservation of application, identity, quantifiers and lambda abstraction. For quantifiers, use the domain bijection at each future point; for abstraction, the naturality just proved ensures the same interpretation along every future arrow, so equality is intensional, not merely current coextension.

Consequently the lift is an automorphism of the pointed action/Henkin model's logical structure, with t fixed pointwise. If b,c are different from a distinguished individual a, injectivity keeps all their future counterparts different, so the automorphism fixes a and every pure term T(a).

### 13.2 SP consequences

The profile-root proof of §10 now works with G in place of F. Its actual G is false: pure Max requires the possibility of a C-countermodel to ND_e, so it refutes □ND_e. At any future point where G holds, §13.1 fixes the profile T(a). Thus SP forces, for every relational τ,

    ∀a∀X^τ [ G ≤ ∀b^e c^e
      ((b≠a∧c≠a) → Sw_τ(b,c,X)=X) ].              (G-Swap-Inv)

For each finite k, the exact same finite equality-pattern formula (F-Sym) holds with G replacing F throughout. Its coefficient propositions are still ∃ȳ(δ_π(a,ȳ)∧X[ȳ]); finite permutations fixing a are transitive on realizable finite tuple patterns at each G-point, and this invariance holds at all further points.

The order, injection and group bounds of §12 also strengthen by replacing F with G. They use only invariance under the displayed individual swaps, not two-valuedness of the entire proposition domain. Thus an old binary relation cannot become a strict linear order on three individuals at a G-target; an old injective total selfmap must be surjective there; and an old group graph cannot have five individuals there.

The homogeneity theorem (Hom) and the unique pointed-completion conclusion of §11 likewise extend from C+F to C+G. This does not imply G at an SP point; Max already refutes G there.

### 13.3 Why bare ND_e is not enough

There is a concrete full action-model counterexample to replacing G by unboxed ND_e in the general homogeneity claim. Take a three-object chain 0→1→2. At 0 let the individual domain be {a,b}; at 1 use {a,b,c}; at 2 use {a,b}. The first transport includes a,b; the second fixes a,b and sends c to a. Use the standard full relational action domains.

At 0, ND_e holds: the two current individuals remain distinct at all future points. But the closed pure one-variable formula

    P(x) := □∀y^e (y=x ∨ □(y≠x))

distinguishes them. P(a) fails because at point 1, c is different from a but later becomes a. P(b) holds because every individual distinct from b, at every reachable point, remains distinct from b. Hence root ND_e does not make all current individuals pure-indiscernible.

The failure is exactly the absence of injectivity at later sources: the middle-to-terminal map merges c and a. A root-level swap of a and b cannot commute with that transport. It would be invalid to extend the Fregean or G-local symmetry argument using only current ND_e.

## 14. Every product embedding has an injective ultraproduct quotient

The finite-product argument in this section was supplied by the parent research agent and independently checked here. The infinite-product extension is an immediate filter argument.

Let N be the full logical term-operation algebra of a genuine pointed C model. Let h_i:N→A_i be sorted homomorphisms of that term signature into arbitrary sorted algebras, and suppose their joint map h:N→∏_i A_i is injective. The target algebras need not carry truth valuations or satisfy C outside the images of the h_i.

For any distinct same-type pair x,y in N, put

    S_(x,y) := {i : h_i(x)≠h_i(y)}.

**Theorem.** The family of all S_(x,y) has the finite-intersection property.

Proof. Take finitely many distinct pairs (x_j,y_j), possibly of different types, and put E=∨_j eq(x_j,y_j) in N_t. The proposition E is actually false in N, because every listed pair is distinct. In particular E≠top. Suppose no coordinate separates all the pairs. At each i, some j has h_i(x_j)=h_i(y_j). Because h_i preserves the identity-former,

    h_i(eq(x_j,y_j))=eq(h_i(x_j),h_i(y_j))
                      =h_i(eq(x_j,x_j))=h_i(top).

The last equality uses the C identity eq(x,x)=top, which follows by Logical Equivalence from reflexivity. The C Boolean absorption identities, transported by h_i, then give h_i(E)=h_i(top). Thus h(E)=h(top), contradicting injectivity and E≠top. □

If I is finite and no h_i is injective, choose for each i a pair collapsed by h_i. The intersection of their separation sets is empty, contradicting the theorem. Therefore any embedding of a genuine C term algebra into a finite product has an injective coordinate projection. In particular a finite pullback or restricted subproduct can repair the mixed-selector failure only by retaining one faithful coordinate. Equivalently, these C algebras are finitely subdirectly irreducible for the full logical term signature.

For arbitrary I, choose an ultrafilter U containing every S_(x,y). The composite

    N → ∏_i A_i → (∏_i A_i)/U

is injective, because every distinct pair remains distinct modulo U. Thus every product embedding of a genuine C term algebra has an injective ultraproduct quotient.

This conclusion is algebraic. The selected ultrafilter is not claimed to preserve N's actual truth valuation, even if the factors separately have C truth valuations. The result therefore sharpens the obstruction to a product construction without resolving the missing Henkin-and-truth expansion in §4.

## 15. Target definability does not evade the old-parameter symmetry

Let G=□ND_e as in §13. Fix an SP point, an original individual a, and finitely many original parameters X_1,…,X_m of relational types. At a G-target, every finite individual permutation fixing the transported a extends to a logical automorphism of the entire target Henkin structure. By (G-Swap-Inv) this automorphism fixes the transported X_i, even though it may move newly available entities.

Consequently, for every formula φ(x,a,X_1,…,X_m) of the pure logical language, allowing arbitrary quantification over newly available entities and arbitrary modal subformulas, SP proves the corresponding instance of

    ∀a∀X_1…X_m [G ≤ ∀x∀y
      ((x≠a ∧ y≠a) →
        (φ(x,a,X_1,…,X_m) ↔ φ(y,a,X_1,…,X_m)))].   (Orbit-Ind)

More generally, tuples having the same equality pattern relative to a satisfy the same formulas over the transported original parameters. The proof is the finite-permutation automorphism argument, now applied to the whole formula rather than merely to atomic application of an original relation. The action on the future/coslice structure in §13 ensures preservation of modal formulas as well as actual first-order truth.

This gives a useful uniqueness test. Suppose a target formula ψ(Y,a,X_1,…,X_m) has exactly one relational witness Y. Every such automorphism takes Y to another witness while fixing all parameters, so uniqueness forces Y to be invariant. Hence a uniquely target-definable strict order on all individuals still requires at most two individuals, and a uniquely target-definable group operation still requires at most four. These conclusions apply even if Y itself is newly available at the target. Likewise, at a target with at least three individuals, any uniquely definable individual over the transported original parameters must be the transported a.

The uniqueness assumption must use only those fixed parameters. A newly available order can itself serve as an additional nonfixed parameter and distinguish individuals; that situation is not covered. Nor does a boxed assertion that a unique witness exists imply that a present witness transports to it. For that inference one must separately prove persistence of the witness property. If persistence is proved, the transported witness is already subject to (G-Swap-Inv); if only target uniqueness is proved, the preceding automorphism argument gives the same invariance directly. Thus neither route produces a forbidden large order or group from old invariant data. Any proposed pure or old-parameter uniqueness premise whose G-target witness would be such a structure is itself incompatible with a sufficiently large target.

These results explain a broad failure of the attempted contradiction strategy. SP can require a G-possibility with arbitrary large orders or groups, but those existential witnesses may be new and nonunique over the original data. Pure logical comprehension from old parameters, or unique definability over them, cannot supply the asymmetry needed to turn those fresh witnesses into forbidden old structures.

## 16. Exact finite rank at every relational type

This extends the parent's proposition-rank theorem in `sp-finite-profile-rank-20261022.md` to every relational type. It also permits the localizing proposition to contain the one distinguished individual variable.

Fix a pure formula A(x) whose only possible free variable is x:e; the closed case is included. Fix a relational type τ=σ_1…σ_l t. Add fresh constants a:e and c_i:σ_i, and let S_(A,τ) be the set of complete consistent theories extending

    C(a,c_1,…,c_l) + A(a).

The constants c_i are argument parameters; they are not a change to the reference pure Max schema. For l=0 this is the pointed proposition completion space. All counts below are external finite counts.

Let Width_r^τ(A(a)) assert that the Boolean interval below K_τ(A(a)) has no r+1 pairwise disjoint nonzero elements. It is a universal finite Boolean combination of typed identities. Put

    U_r := ∀a^e Width_r^τ(A(a)).

**Theorem.** Pure Max plus U_r is consistent if and only if S_(A,τ) has at most r members. If S_(A,τ) has exactly finite m members, pure SP makes every such interval, for every current a, the Boolean algebra with exactly m atoms and 2^m elements. If S_(A,τ) is infinite, pure Max already makes every such interval fail every fixed finite width bound.

### 16.1 The lower bound already follows from Max

If S_(A,τ) has r+1 distinct members, choose finite Boolean cells χ_0(a,c̄),…,χ_r(a,c̄) separating them. These cells may be chosen pairwise contradictory, with each A(a)∧χ_j(a,c̄) consistent. Define the pure relation terms

    W_j(a) := λȳ.[A(a)∧χ_j(a,ȳ)].

The pure one-individual-variable sentence A(a)∧∃ȳχ_j(a,ȳ) is C-consistent. Unary Possibility+ therefore makes it possible of every actual a in every Max model. By the projection/nonzero equivalence from §5.2, W_j(a) is nonzero. Their pairwise meets are bottom by the C-provable incompatibility of the cells, and they lie below K_τ(A(a)). Thus Width_r^τ(A(a)) fails for every current a. This proves necessity and the infinite case.

### 16.2 Finite completions eliminate the free actual extension

Suppose S_(A,τ) has exactly finite m members. Forgetting the constants c̄ maps this space onto the complete C(a)+A(a) theories: every model of any such theory can interpret the finitely many c_i because all type domains are nonempty. Hence there are at most m pointed completions without c̄.

As in the parent's rank proof, A(a) is therefore false for every actual a in every pure Max model. Otherwise an actual a realizing A would satisfy one of finitely many isolating formulas, giving a consistent recursively enumerable complete extension of C(a) that contains every pure Max axiom. The supplied undecidability argument rules that out. This step uses pure Max only; it does not assume a Max schema with the c_i or a added to its metalinguistic language.

At the singleton profile root, K_τ(A(a)) consequently has empty actual extension. Every element below it also has empty actual extension. Thus the freely chosen root extension coordinate contributes no additional elements to this interval.

### 16.3 The profile interval has exactly m atoms

Choose isolating Boolean cells χ_1(a,c̄),…,χ_m(a,c̄) for the m completions and use the relation terms W_j(a) above. Their profiles are nonzero, disjoint, and exhaust K_τ(A(a)). Every root relation X^τ has a profile T(a). Each complete theory C(a,c̄)+A(a)+χ_j(a,c̄) decides the formula T(a)[c̄]. Therefore the localized relation K_τ(A(a))∧X is the join of exactly those W_j whose theory includes that formula.

This is an intensional identity, not merely agreement at the current arguments of one component. Completeness gives the corresponding C-theorems A(a)∧χ_j(a,c̄)→T(a)[c̄], or their negated alternatives. These may be necessitated and universally closed over c̄. Modalized extensionality then identifies the localized relation profiles at every component and every future argument tuple. Since their root extensions are all empty, the root entities themselves agree.

Thus the profile-root interval contains exactly the 2^m joins of the m nonzero cells, proving Max-consistency of U_m and hence U_r for every r≥m. For m=0 the localizing formula is C-inconsistent and the interval is trivial. This proves sufficiency.

Finally U_m is a pure universal Boolean identity sentence, so SP reflects it. The lower-bound cells from §16.1 exist already under Max; with Width_m they must be atoms and exhaust the interval. This proves the exact SP rank assertion.

### 16.4 Connection with the finite orbit counts

For A=A_n=F∧Exactly_n(e), the complete C(a,c̄)+A_n theories correspond exactly to the orbits of the tuple c̄ under the finite hierarchy automorphisms fixing a. Section 9 proves that these automorphisms are precisely the individual permutations fixing a and that every orbit is definable by a pure a-term. Therefore |S_(A_n,τ)| is exactly the orbit count o_(n,τ) already calculated there.

The present theorem explains those counts as instances of a uniform completion-space criterion. It also applies to non-Fregean A, whenever its indicated completion space is finite; no permutation classification is needed in that case. It does not assert finite rank when the completion space is infinite, and it does not establish consistency of pure SP.

## 17. Explicit non-Fregean complete cells: finite full S5 hierarchies

This section gives an explicit family to which the finite-rank theorem applies outside F. The completeness argument is original to this note (misc); the standard full action construction and the implications from boxed ND used in it are recorded sources, not claims of new published results.

For positive standard integers n,m, let E_r^σ say there are exactly r entities of type σ and define

    B_(n,m) := □ND_t ∧ □E_n^e ∧ □E_(2^m)^t.

**Claim.** C(a)+B_(n,m), with one individual constant a, is consistent and complete. Consequently pure SP forces Atom_t(B_(n,m)). For m≥2 these atoms lie below ¬F. The cells for different ordered pairs (n,m) are pairwise disjoint, so SP has infinitely many distinct pure weak atoms below ¬F, as well as the familiar finite Fregean cells below F.

### 17.1 Recorded inputs and the consistency model

The following implications are recorded as proved:

1. □ND_t implies boxed ND at every type (`necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r`, Classicism Proposition 2.2, p. 22).
2. Boxed ND at every type implies boxed BF at every type (`necessary-distinctness-necessary-r-implies-necessary-barcan-r`, Classicism Proposition 2.3, p. 22, with the Prior–Lemmon argument).
3. Boxed BF implies boxed Functionality (`necessary-barcan-r-implies-necessary-functionality-r`; its unboxed version is `barcan-r-implies-functionality-r`).

Functionality here says that operations agreeing in their output ENTITIES on every argument are identical. It is not the stronger assertion that relations with the same actual true instances are identical. No actual-truth Extensionality or Fregean Axiom is used below.

For consistency take the full action model on the finite indiscrete groupoid with m objects (exactly one arrow between any ordered pair), and a constant n-element individual domain with identity transports. This is the finite version of the full S5 construction described in the recorded `full-infinite-s5` model; the full action construction itself is Classicism §3.5, pp. 58–61. Propositions at each point are the subsets of the m-object world set, hence number 2^m. All arrows are invertible, so all entity transports are bijective and boxed ND holds. The individual and proposition cardinalities are constant. Therefore B_(n,m) holds, and a can name any individual.

### 17.2 Every higher type is a full finite function set

Consider any pointed C model satisfying B_(n,m). Its proposition domain is the finite Boolean algebra with 2^m elements; C supplies the Boolean algebra laws. Its individual domain has n elements. By the recorded inputs, ND and Functionality hold at every type, and the corresponding boxed principles are available when needed.

Induct on the relational type construction. Assume the domains D_σ and D_ρ are already finite, with ρ relational. Application gives a map

    D_(σρ) → (D_ρ)^(D_σ).

This is injective by Functionality. To prove surjectivity, enumerate D_σ as c_1,…,c_N and take any external assignment c_i↦d_i in D_ρ. ND at σ makes the identity proposition eq_σ(c_i,c_j) bottom when i≠j, while reflexivity makes it top when i=j. More generally every identity proposition at σ is top or bottom: true identity gives top by NI/reflexivity, and false identity is necessarily false by ND. Hence the admitted term

    λx^σ. ⋁_(i=1)^N (K_ρ(eq_σ(x,c_i)) ∧_ρ d_i)

has output entity exactly d_i at c_i. Henkin closure supplies it, and Functionality identifies it with the requested function. Thus application identifies D_(σρ) with the ENTIRE finite function set (D_ρ)^(D_σ).

This induction works equally when σ=e and uses no forbidden individual-output function type: the output ρ is always relational. It establishes finiteness and fullness at every admitted type. It does not identify distinct output propositions merely because they have the same actual truth value.

### 17.3 The logical operations are determined, including quantifiers and lambda

At every type, identity is the crisp top/bottom operation just described. Boolean operations are those of the proposition algebra, extended pointwise to relational outputs. Application is evaluation. Lambda abstraction is the unique function given by its beta values, because Functionality holds. It remains to check that an otherwise nonstandard intensional quantifier operation cannot distinguish two models with the same finite hierarchy.

Let c_1,…,c_N enumerate any actual type domain D_σ. At the point,

    ∀x^σ ⋁_i x=c_i

holds. NI makes each of these true identity alternatives necessary, yielding ∀x□∨_i(x=c_i). BF at σ then yields □∀x∨_i(x=c_i). Thus the enumeration is necessarily exhaustive; its displayed members are necessarily distinct by ND. For any formula P(x), necessary finite enumeration gives

    □[(∀xP(x)) ↔ ⋀_iP(c_i)].

The proposition Boolean algebra identity criterion turns this necessary equivalence into identity of the two proposition terms. Hence universal quantification is exactly the finite meet operation; existential quantification is exactly finite join. This proves the assertion for every type, not only e and t.

Consequently the entire many-sorted logical term structure is determined by: an n-element individual set; a Boolean algebra with 2^m elements; every admitted higher type its full finite function set; identity crisp; quantifiers finite meets/joins; application evaluation; and lambda its beta-determined function. This is an identification of the full logical signature, not merely of its reduct to actual application or first-order equality.

### 17.4 Actual truth and the distinguished individual do not split the theory

The model's actual truth valuation on the finite proposition Boolean algebra is a Boolean ultrafilter. It is therefore the ultrafilter generated by one of its m atoms. The automorphism group of the finite Boolean algebra permutes those atoms transitively. Thus for any two such pointed models, choose a Boolean algebra isomorphism sending the first truth atom to the second; choose an individual bijection sending the first interpretation of a to the second. Extend these maps recursively to the full function domains by conjugacy.

The resulting sorted isomorphism preserves application, crisp identity, Boolean operations, finite quantifiers, and beta-determined lambda. It preserves actual truth because it sends the truth atom to the truth atom. It therefore preserves every formula in the full language, including its modal abbreviations and arbitrarily high but finite types. All models of C(a)+B_(n,m) are isomorphic in this complete pointed logical sense. The displayed finite full S5 model gives existence, so C(a)+B_(n,m) is complete and consistent.

This isomorphism argument does NOT say that the actual truth atom is denoted by a pure proposition term. In a homogeneous finite S5 model, closed pure proposition terms are invariant under changing the evaluation world and can denote only bottom or top. The isomorphism comparison is allowed to move the truth atom along with the point; that is precisely why its chosen position does not split the pure pointed-individual theory.

### 17.5 Consequences under SP

By the finite-rank theorem, B_(n,m) is a weak propositional atom at every SP point. It is nonzero already under Max, since the consistency model proves B_(n,m) C-consistent. Different ordered pairs give incompatible actual cardinality statements, so their conjunction is bottom by C. For m≥2, B_(n,m) entails that there are more than two propositions and therefore entails ¬F. The corresponding identity B_(n,m)≤¬F follows by Logical Equivalence/necessitation of that C implication.

Thus, conditionally on SP consistency, the interval below ¬F contains infinitely many pairwise disjoint pure-named weak atoms. None is a strong world by §5, and §6 gives distinctness-preserving possibilities where any finite selection survives and simultaneously acquires atomless intervals. The apparent tension is resolved by the same absence of BF at the original SP point: new entities at targets can split old weak atoms.

The general all-type rank theorem also applies to these cells. The complete theories with argument constants c̄ correspond to orbits of their argument tuples under the automorphisms of the finite hierarchy fixing a and the actual truth atom. The base group is S_(n−1)×S_(m−1), acting recursively on the full function hierarchy. In particular, for τ=tt, the argument p is a subset of the m Boolean atoms. Its orbit is determined by whether it contains the distinguished truth atom and how many other atoms it contains. There are 2m orbits. Hence SP makes the B_(n,m)-localized type-tt Boolean interval have exactly 2m atoms and 2^(2m) elements. For τ=et, the count is one argument orbit if n=1 and two if n≥2, giving two or four interval elements respectively.

### 17.6 Explicit pure witnesses to failure of Functionality

Fix m≥2 and write b=B_(n,m). Since b is a finite conjunction of boxed propositions, S4 proves b↔□b, and Logical Equivalence gives b=□b. In C, any weak atom b with this identity satisfies

    ∀p [b∧p = b∧□p].                            (LocalCollapse)

Indeed atomicity gives b≤p or b≤¬p. In the first case normality gives □b≤□p, so b≤□p and both displayed sides are b. In the second case □p≤p makes both sides bottom. Thus SP proves (LocalCollapse).

Nevertheless the two CLOSED PURE operators

    f := λp.[b∧p],       g := λp.[b∧□p]

are distinct already under pure Max. In the finite full S5 B_(n,m) model, b=top and a proper nonzero proposition p has □p=bottom, so f(p)≠g(p). Therefore f=g is not a C-theorem, and its Max disequality instance gives f≠g. Hence SP yields the concrete failure

    (∀p fp=gp) ∧ f≠g.

This does not use actual-truth coextension: the outputs agree as proposition ENTITIES on every current input.

One can count the entire failure inside this finite interval. The Boolean algebra L=[bottom_tt,K_tt(b)] has 2m atoms by §17.5. Evaluation on the current proposition domain factors exactly through the two arguments bottom and top. To see this, atomicity and b=□b imply that at every b-true future point each transported old proposition is literally bottom or top. Thus a localized operator is pointwise zero on all current arguments exactly when its values at bottom and top are both bottom. Each endpoint evaluation picks one distinct atom of L; the other 2m−2 atoms are invisible on every current argument. Consequently there are exactly 2^(2m−2) localized operators X satisfying

    ∀p Xp=bottom,

although only one of them is bottom_tt. In particular m=2 already gives three distinct nonzero such operators.

For a direct description of the 2m atoms, at the B_(n,m) targets let C_k(p) say that exactly k Boolean atoms lie below p. The possible pairs (k,ε), where ε is the truth of p at the current world, are (k,1) for 1≤k≤m and (k,0) for 0≤k≤m−1. Their characteristic old operators are

    λp.[b∧C_k(p)∧p]       and       λp.[b∧C_k(p)∧¬p],

respectively. The endpoint atoms are (m,1) and (0,0); all the remaining ones vanish on every current input. They remain nonzero as entities because newly available arguments at future B_(n,m) points distinguish them. This is an explicit finite description of the Henkin witness gap, not a contradiction with C.

Audit note: the finite-hierarchy and completeness argument in §§17.1–17.5 was independently checked by the sibling Codex subagent `henkin_minimal` on 22 October 2026, with all substantive steps accepted. This is an additional machine mathematical review, not a human check or formal verification. The multiplicity calculation in this subsection has not received that separate audit.

## 18. Open weak atoms, persistent empty relations, and a precise Barcan failure

Call b open here only as shorthand for the identity b=□b. This section uses no topological assumption. Every B_(n,m) has that identity.

### 18.1 General local settlement law

C proves

    Atom_t(b) ∧ b=□b →
      ∀p [b≤(p=bottom ∨ p=top)].                  (LocalSettlement)

Indeed atomicity gives b≤p or b≤¬p. In the first case normality and openness give b≤□p=(p=top). In the second they give b≤□¬p=(p=bottom). This proves the displayed identity inequality in either case. It also recovers LocalCollapse and the vanishing of every proper-proposition test below b.

For b=B_(n,m) with m≥2, the pure proposition b is nonzero under Max, SP makes it a weak atom, and C proves b≤¬F. Yet F is equivalent to ∀p(p=bottom∨p=top). Therefore SP proves the specific closed pure pattern

    ∀p □(b→(p=bottom∨p=top)),
    ¬□∀p (b→(p=bottom∨p=top)).                  (PureBFfailure)

For the second line, its negation would give b≤F, contradicting b≤¬F and b≠bottom. This is a named pure instance of failure of BF_t; it uses no arbitrary actual relation parameter. In Boolean-order language, b is below every currently indexed Settled(p) but is disjoint from their object-language universal quantification. The object-language universal is therefore not the greatest lower bound of that current family.

### 18.2 A pure persistent relation with every current value bottom

Fix the same b and put

    h := λp.[b ∧ p≠bottom ∧ p≠top].

C proves Persistent(h). To see this, at any point where hp is true, b is true and hence remains true necessarily. The b conjunct supplies □ND_t; since p is different from bottom and top there, these two disequalities remain true necessarily. Thus hp→□hp is a C-theorem, uniformly in p. Legitimate necessitation yields □∀p(hp→□hp), the definition of persistence.

The finite S5 model for b has proper nonzero propositions, so h≠bottom_tt is a Max consequence. In contrast (LocalSettlement) makes hp=bottom for every current p under SP. Furthermore C proves

    (∃p hp) = b:

the left side implies b, and b entails the existence of a proper nonzero proposition because 2^m≥4; apply necessitation and the proposition identity criterion to that C equivalence. Thus

    Persistent(h) ∧ h≠bottom_tt ∧
    (∀p hp=bottom) ∧ ((∃p hp)=b)

holds under SP. The existential proposition is nonzero but actually false, because b is false in every Max model. Future witnesses, rather than any current true instance, account for its nonzero value.

Since h has no current true instances, WeaklyInextensible(h) would imply h≤bottom_tt by taking the bottom relation as the candidate upper bound. Hence h is not weakly inextensible, not inextensible, and not weakly rigid, despite being persistent. This does not refute Persistent Comprehension, Weakly Inextensible Comprehension, or Weak Rigid Comprehension: bottom_tt is a rigid coextension of h. A comprehension scheme asks for some coextensive representative, not for the original relation itself to have the relevant property.

### 18.3 What weak inextensibility would force on an old representative

For any current Y^tt, WeaklyInextensible(Y) together with (LocalSettlement) implies

    K_tt(b)∧Y ≤ λp.[b∧(p=bottom∨p=top)].

Take Z:=λp.[b→(p=bottom∨p=top)]. By LocalSettlement every current p satisfies □Zp, so the antecedent in WeaklyInextensible(Y) holds for this Z irrespective of which p satisfy Y. Consequently Y≤Z; meeting with K_tt(b) gives the claim.

If Y is also persistent and coextensive at the current point with λp.p, this bound becomes equality. Current top is a Y-instance, and current ¬b is a Y-instance because Max makes b false. Persistence preserves both instances. At a b-true target, the transported b is top (because b=□b), so the transported ¬b is bottom. Thus Y holds necessarily of both bottom and top there, while the preceding bound excludes every proper proposition. Necessary pointwise reasoning gives

    K_tt(b)∧Y = λp.[b∧(p=bottom∨p=top)].

This is compatible with the finite S5 profile spectrum: it is exactly one of its admitted pure localized operators. Hence the old-parameter constraints examined here restrict the possible weakly rigid truth representative, but do not prove its nonexistence or refute Weak Rigid Comprehension. No inconsistency of pure SP follows from these arguments.

### 18.4 Functionality still fails for provably persistent pure operators

The pair h,bottom_tt strengthens the preceding f,g example: BOTH are closed pure operators whose persistence is proved in C, while SP proves

    ∀p hp=bottom   and   h≠bottom_tt.

Thus even Functionality restricted to provably persistent pure operators is incompatible with SP. Equivalently the empty current property of propositions has at least two persistent representatives, one of which is a nonzero pure operator. A variant of Persistent Comprehension demanding a UNIQUE persistent coextension is therefore refuted already at this one pure empty-property instance. The ordinary recorded Persistent Comprehension principle demands existence only and is not refuted by this observation.

Weak rigidity behaves differently for a reason visible in C itself. If two weakly rigid relations are actually coextensive, persistence of one supplies the necessary upper-bound condition in the weak inextensibility of the other. This gives both algebraic inclusions and hence identity. The nonzero h necessarily fails the weak inextensibility part; no conflict with this valid weak-rigidity extensionality argument arises.

For completeness, persistence can be counted exactly inside the b-localized tt interval. Its 2m Boolean atoms are the input-orbit atoms (k,ε) of §17.6. At a b-true finite S5 point, a persistent operator must have, for each fixed proposition input, a necessary output, hence output bottom or top. For each proper cardinality k=1,…,m−1, the two atoms (k,0) and (k,1) must therefore be included together or omitted together: selecting only one makes the output change truth between accessible worlds of the finite S5 cluster. The endpoint atoms (0,0) and (m,1) are independent choices. Conversely each such selection is the pure operator b times a disjunction of crisp atom-cardinality tests C_k(p), so it is persistent in C.

There are m+1 independent choices, giving exactly 2^(m+1) persistent elements among the 2^(2m) localized operators. All localized operators are weakly persistent at the SP point, since b is actually false and they have no current true instances. Only bottom is weakly inextensible, by the empty-instance argument. Among the 2^(2m−2) operators vanishing as entities on every current input, exactly 2^(m−1) are persistent; they are the selections of proper cardinality tests. For m=2 these numbers are respectively 16 total, 8 persistent, 4 pointwise-zero, and 2 persistent pointwise-zero (bottom and h).

These classifications follow from the finite profile spectrum and the explicit finite S5 models. They do not rely on an assumed truth extensionality principle, and they provide no additional inconsistency of SP by themselves.

## 19. A uniform pure persistent counterexample at every relational input type

Fix once and for all b=B_(1,2). Its full finite S5 targets have one individual and a four-element proposition Boolean algebra. Define the closed pure operation

    ν(p) := □p ∨ (◇p∧¬p).

At a b-target, ν fixes bottom and top and interchanges the two Boolean atoms. It is the nonidentity Boolean algebra automorphism. It moves the actual truth atom, so it is an automorphism of the FULL LOGICAL ALGEBRA, not of its designated actual-truth valuation. The distinction matters below.

### 19.1 Lifting the Boolean automorphism to all types

Let S_e be the identity semantic action on the singleton individual set; no ee term is introduced. Let S_t=ν. For each relational type σ=α_1…α_k t, define the closed pure transformer

    S_σ(X) := λx_1…x_k.
       ν(X[R_(α_1)(x_1),…,R_(α_k)(x_k)]),

where R_e(x)=x syntactically and R_α(x)=S_α(x) for relational α. This recursion is on strictly lower argument types. At a b-target it is the ordinary conjugacy lift of the involution ν to full finite function spaces. Each S_σ is therefore an involution.

The lifted sorted action preserves application, crisp identity, Boolean operations, finite quantifiers, and beta-determined lambda. Boolean automorphisms preserve finite meets/joins, and the finite function domains are permuted bijectively. Thus it is an automorphism of the entire logical term algebra described in §17. Since the individual domain is singleton, it fixes any interpretation of the distinguished a. Therefore it fixes EVERY pure a-term T(a) at every type.

This last assertion concerns term values, not actual truth of arbitrary formulas with moved parameters. A uniquely actual-truth-definable Boolean atom need not be fixed, since ν moves the truth valuation. The truth-preserving uniqueness argument in §15 must not be applied to this different automorphism.

### 19.2 SP fixes every old entity under this local action

The singleton profile-root Max model satisfies, for every fixed relational σ,

    ∀X^σ [b≤(S_σ(X)=X)].                         (WorldSwap_σ)

Every X has a pure a-term profile, which is fixed at every b-target by §19.1. The implication b→S_σ(X)=X holds at the root because b is false there, and it holds at all component points where b is true by that profile calculation. Hence its necessity, equivalently the displayed identity inequality, holds. This proves Max-consistency of the universal identity sentence.

UMax reflection therefore makes (WorldSwap_σ) a consequence of SP. It is an explicit non-Fregean identity law on arbitrary current higher-type entities, not merely on pure named ones.

### 19.3 Uniform persistent ghosts

Define the closed pure predicate

    k_σ := λX^σ.[b∧S_σ(X)≠X].

C proves Persistent(k_σ): b is open, and b supplies boxed ND at σ, so any true instance has its disequality and its b conjunct necessary. The proof may be universally closed and necessitated in C.

For EVERY relational σ, k_σ is nonzero in the finite S5 b-model. Choose a proposition atom q and let X=K_σ(q), the constant relation at type σ (for σ=t take X=q). The lifted action sends X to K_σ(νq), which differs from X. Thus k_σ has an instance there. Consequently k_σ=bottom_(σt) is not a C-theorem, and Max proves its disequality.

But (WorldSwap_σ) makes every current k_σ(X) literally bottom under SP. We have proved, uniformly over all relational input types σ,

    Persistent(k_σ),    k_σ≠bottom_(σt),
    ∀X^σ k_σ(X)=bottom_t.

For any relational output type ρ, let

    H_(σ,ρ) := λX^σ.K_ρ(k_σ(X)).

It too is closed pure and C-provably persistent as a relation of its full terminal type. SP makes each current output entity bottom_ρ, but Max makes H_(σ,ρ) distinct from bottom_(σρ). Thus every Functionality instance with RELATIONAL input σ and relational output ρ has a counterexample consisting of two closed pure C-provably persistent operators.

### 19.4 The sharp contrasting case: closed pure individual-input operators

Let f,g be closed pure terms of type eρ, with ρ relational. Pure Max proves the corresponding restricted Functionality assertion; indeed it proves

    (∃x^e fx=gx) → f=g.

Here is the exact metatheoretic argument. If C proves f=g, there is nothing to show. Otherwise C(a) cannot prove fa=ga: such a proof could first be generalized to the C-theorem ∀x fx=gx, then that C-THEOREM could legitimately be necessitated, and modalized Functionality would give the forbidden C-theorem f=g. Thus the pure one-individual-variable formula fx≠gx is C-consistent. Unary Possibility+ under Max yields ∀x◇(fx≠gx). NI gives the fixed-C theorem ◇(fx≠gx)→fx≠gx. Hence Max in this case proves ∀x fx≠gx, proving the assertion.

No optional pointwise equality was abstracted or necessitated in this proof. The only necessitated pointwise equality was a hypothetical C-theorem used in the metatheoretic contrapositive.

This restriction requires CLOSED pure f,g. An additional original individual parameter can distinguish the original individual from future individuals, and SP still refutes unrestricted Functionality with input e. Nor does the statement cover simultaneous actual evaluation on two or more individual arguments: a pure binary predicate can vanish on all current equal tuples while acquiring instances on new distinct tuples. The sharp boundary here concerns a single individual input with ENTITY-valued equality of its full output.

An explicit persistent example makes the last distinction concrete. Put c=B_(2,1) and j:=λx^e y^e.[c∧x≠y]. C proves persistence, since c is open and supplies boxed ND_e. A finite two-individual c-model makes j nonzero, so Max proves j≠bottom_(eet). SP's singleton-individual consequence makes every current j(x,y) literally bottom. Nevertheless Max proves that, for EVERY current x, its unary section λy.j(x,y) is a nonzero entity of type et: apply the theorem just proved to the closed pure operators j:e(et) and bottom_(e(et)), or use the two-individual countermodel for their a-values directly. Thus current terminal-value vanishing and nonzero entity-valued sections coexist; the argument does not silently identify those two notions of equality.

## 20. Why the persistent ghost alone cannot prove inconsistency

The complete ghost configuration from §§18–19 is already realized in the genuine singleton profile-root Max model. Its finite B_(n,m) intervals are atomic by §§16–17, so the same LocalSettlement and WorldSwap proofs give all-current-value vanishing; the finite S5 components give nonzeroness; persistence is a C-theorem. Thus C plus pure Max plus these ghost facts is consistent under the supplied profile-root construction.

This is a decisive check on the focused contradiction attempt. No principle derived in C solely from purity, definability, persistence, and the displayed ghost equations can collapse the specific ghost to bottom: that genuine C+Max model is a counterexample to such a proposed principle. A contradiction would have to use a further SP consequence absent from this root, not only reinterpret the already established ghost facts.

The familiar local hypotheses that DO collapse h are explicit and optional:

- WeaklyInextensible(h), taking bottom as its necessary upper bound of the empty current extension.
- The single BF-dual instance ◇∃p hp→∃p◇hp. Its antecedent holds because (∃p hp)=b≠bottom, while every disjunctively witnessed current possibility is false because hp=bottom for each current p.
- Functionality for the particular pair h,bottom_tt, even if restricted to pure persistent operators.

Ordinary Relational or Functional Choice cannot be applied directly to h: it has no current instance and supplies no current seriality premise. Intensional Choice cannot be applied directly either: it requires □∃p hp, whereas the existential proposition here is b≠top. Existence-only persistent or weakly rigid comprehension is not contradicted, since bottom is a suitable coextension. These are precise candidate eliminations, not a proof that all conceivable choice/comprehension combinations are compatible with SP.

## 21. Compatibility with essentiality and the exact algebraic/Henkin boundary

The parent's essential-extension note (`sp-essential-extension-20261022.md`) considers the full term-operation algebra A of a genuine Max model, its common pure a-term subalgebra B, and a maximal congruence whose restriction to B is equality. Its quotient Q contains B essentially: every nonidentity congruence identifies two distinct B-elements. The sibling's `sp-henkin-minimal-20261022.md`, §§16–20, establishes identity-correct Boolean truth extensions and analyzes which actual existential witnesses survive subsequent quotients. Neither construction currently establishes Henkin completeness of Q.

### 21.1 Positive reflection does not require a Henkin truth interpretation

There is a direct strengthening of the positive-reflection step. Suppose a finite conjunction of term equations over B has an algebraic solution in Q. Its identity-valued conjunction is top, because each satisfied equation has reflexive identity value top. Let E(a) be the internal existential proposition obtained by replacing the B-parameters by their pure a-terms and quantifying the solution variables. Existential-introduction inequalities are C equations and hold in every quotient; they give top≤E(a), hence E(a)=top in Q.

But E(a) belongs to the preserved subalgebra B. Its equality to top is therefore C(a)-provable, and C(a) proves E(a). The already established positive profile-witness extraction supplies a solution of the original equations by pure a-terms. Thus every positive existential equation system realized in Q is realized in B, without choosing or using actual truth on Q.

If the original finite identity diagram includes disequalities, use essentiality exactly as in the parent's finite-congruence-chain proof. For each negative pair s≠t, a finite polynomial chain from distinct B-elements b,c in the congruence generated by (s,t) supplies finitely many additional positive equations. Reflect the enlarged positive system to B. If its new s,t became equal, every chain step would become equal and force b=c, impossible. This preserves all finitely many negative pairs simultaneously.

Consequently B and Q have the same existential finite-Boolean-identity theory over B. In particular Q already satisfies, algebraically, all universal identity sentences individually consistent with Max. The simultaneous algebraic universal constraints are therefore NOT the remaining construction obstacle. The outstanding obligation is to make the quantified proposition operations agree with actual quantification under an identity-correct Boolean truth ultrafilter on Q. This stronger reflection argument was independently audited by the sibling agent; it is ordinary mathematics, not a human or formal verification.

### 21.2 Density does not expose a current argument for a ghost

The essentiality/modal-density argument can give a nonzero pure proposition below the disequality of two distinct operators. This does not give a current argument distinguishing their values. For the pure ghost pair h,bottom_tt, its disequality is itself already a nonzero pure proposition. It is possibility-fixed by NI. In fact every nonzero possibility-fixed proposition r is actually true in any genuine C model, simply because r=◇r and ◇r is the proposition r≠bottom.

There is no missing application witness in this reasoning: actual pointwise coextension is not a congruence for the FULL term signature. The identity-forming operation itself can distinguish coextensive entities. Thus essentiality may detect a ghost through its pure intensional identity while leaving every current application zero, exactly as the universal identity theory demands.

The internal existential proposition (∃p hp) is b, by §18. Since b=□b and b≠top is a fixed B-disequality, every identity-correct B truth makes b false. Consequently this proposition generates no current existential witness request in a quotient with such truth. Its nonzeroness requires future possible witnesses, which is a different condition.

One must distinguish E_h:=(∃p hp≠bottom). This quantified proposition can be true in a signature-Max model: a named proposition p with h(p)≠bottom is permitted by the finite S5 b-example and the signature Max disequality schema. But every essential quotient algebraically satisfies ∀p hp=bottom, by §21.1 and the individually consistent universal law from §18. If its chosen old B truth contains E_h, that assignment cannot be Henkin-perfect: no current algebraic witness exists. This is an explicit witness-loss region, but it is already excluded by Atom(b), since the LocalSettlement theorem proves Atom(b)→¬E_h. It therefore adds no obstruction after the known pointed-complete atomicity laws have been imposed.

No claim that essentiality is necessary for SP is made. Its usefulness is as a sufficient model-construction criterion, and its truth/witness obstruction remains genuinely open here.

## 22. Boxed unique existence does not supply a transported witness

There is a particularly small pure example explaining why uniqueness alone cannot repair the ghost or swap arguments. Again fix b=B_(1,2), and put

    R(p) := (b∧Atom_t(p)∧p) ∨ (¬b∧p=bottom).

C proves ∃!p R(p). Under b the proposition Boolean algebra has four elements, so exactly one of its two atoms is actually true: their join is top, their meet is bottom, and classical truth is a Boolean ultrafilter. Under ¬b the unique witness is bottom. This is a finite C proof with the whole guard in the theorem, so legitimate necessitation gives

    C ⊢ □∃!p R(p).

Every Max model makes b false (it has only finitely many pointed complete extensions, or use §17 directly). Therefore its unique current R-witness is bottom. On the other hand R(bottom)=¬b as proposition entities, and Max proves ◇b because b is C-consistent. Hence

    Max ⊢ ¬∃p □R(p).

Indeed a necessary R-witness would first be a current witness by T, hence would be bottom, and □R(bottom)=□¬b contradicts ◇b. Pure definability, C-provable unique existence, and even C-provable BOXED unique existence therefore do not force one current witness to remain the witness at future points.

There is also no closed pure term T (nor a pure a-term T(a)) for which C proves R(T). Evaluate at the finite b-model with one individual. The full logical-algebra atom-swap from §19 fixes every such term, so its proposition value is bottom or top. Neither is an atom, so R(T) is false there. This is a failure of a pure term-witness or definite-description property for general actual-truth formulas; it does not contradict the positive IDENTITY witness theorem.

This example is NOT a failure of the recorded Intensional Choice instance for R. That principle asks for a necessarily uniquely instantiated subproperty and permits its unique instance to vary. R itself is already such a subproperty. Nor is R persistent: persistence of its current bottom instance would contradict the preceding calculation. The example isolates precisely why boxed uniqueness, without persistence or another justified transport principle, cannot turn fresh target witnesses into the old witnesses required by the attempted SP contradictions.

## 23. Finite identity exclusions can also have permanent old witnesses

The sibling's finite-observation witness theorem can be strengthened to permit finitely many direct identity tests against old parameters. This identifies a larger fragment in which the quotient construction has no Henkin witness loss.

Let σ=α_1…α_d t be any relational witness type, including t. Let c be old parameters in a term-operation subalgebra D containing B. Fix finitely many old argument tuples s_j(c), and finitely many old entities C_1(c),…,C_k(c) of type σ. Suppose the following dependence assertion is a C-THEOREM:

    [ ∧_j(F[s_j(c)]↔G[s_j(c)])
      ∧ ∧_{r=1}^k((F=C_r(c))↔(G=C_r(c))) ]
          → [φ(F,c)↔φ(G,c)].

Thus φ may inspect finitely many current application truth values and finitely many direct identities of the WHOLE witness with old entities. It need not be extensional in F. The dependence theorem is a real hypothesis; arbitrary modal or quantified tests are not automatically covered by it.

Choose k+1 pure propositions q_l:=□Exactly_l(e), for l=1,…,k+1. Each is open by S4, so C proves q_l=□q_l=eq(q_l,top). They are pairwise distinct in the common B diagram: a one-world full Fregean model with exactly l individuals gives q_l=top and q_j=bottom whenever j≠l. Each q_l also differs from top in B, as a one-world full Fregean model of any different finite cardinality witnesses. Thus pure Max proves these finitely many disequalities. In particular every identity-correct Boolean truth on B makes each q_l false, because q_l=eq(q_l,top) and q_l≠top. For the finite C argument write the guard

    G_q := ∧_l ¬q_l ∧ ∧_{l<l'} q_l≠q_l'.

This reservoir requires only pure Max's term diagram and finite extensional models, not the finite S5 completion theorem or any SP atomicity consequence.

For each finite bit table η on the observations, use the old identity-table relation

    T_η(c) := λu_1…u_d. ∨_{j:η_j=1} [ubar=s_j(c)].

As in the sibling's theorem, only tables consistent with coincident argument tuples need be used by a witness; including all tables in the finite disjunction is harmless. For σ=t, a nullary observed truth bit has the obvious bottom/top tables. Define the finite old candidate family

    C_r(c)                       (1≤r≤k),
    T_η(c) Δ K_σ(q_l)            (all η, 1≤l≤k+1),

where Δ is Boolean symmetric difference at the relational type. C proves that, under G_q, every existential witness for φ can be replaced by one of these candidates.

To prove this, if F=C_r for some r, use that candidate. Otherwise choose η equal to F's observed truth table. Then T_η matches every observation. Because each q_l is false, all k+1 translates T_η Δ K_σ(q_l) have those same current observations. They are pairwise distinct: constant lift is injective, and symmetric difference with a fixed element is an injective Boolean operation. At most k of these distinct candidates can coincide with one of the k forbidden entities C_r. Choose a remaining candidate. Its direct identity tests are all false, exactly like F's, so the stated dependence theorem transfers φ. The converse implication is ordinary existential introduction.

This is a finite first-order case and pigeonhole argument in C, with the complete guard retained. Consequently, if L(c) is the finite disjunction of φ evaluated at the displayed candidates, C proves

    G_q → [(∃F φ(F,c))↔L(c)],

and Logical Equivalence gives the C equation

    G_q∧(∃F φ(F,c)) = G_q∧L(c).

It therefore holds in every algebraic quotient of a C term algebra. Let V be an identity-correct Boolean truth ultrafilter on D extending one on B. The guard belongs to V. If the internal existential proposition belongs to V, one finite disjunct belongs to V and gives a witness already in D. Every later injective term map preserving V preserves that witness permanently. No arbitrary truth of a newly supplied proposition has been assumed.

There is an analogous E_1-guarded form for σ=e…et when the observation part of the dependence assertion is GLOBAL current coextension rather than finitely many named observations. Under E_1 every F has the actual extension of one of the two constant relations. Replace T_η by bottom_σ or top_σ and repeat the same translates/identity-exclusion argument. The whole guarded theorem is proved in C before equationalization.

This result covers finite direct identity sensitivity, including negative identity literals involving the witness itself. It does not cover arbitrary tests such as an identity involving an unbounded operation of F, nor a quantified family of forbidden entities, unless a separate finite-dependence reduction is proved. The remaining Henkin gap must therefore involve more than finitely many actual observations together with finitely many direct comparisons against old entities.

### 23.1 Several witnesses and their mutual identity pattern

The same method handles a finite tuple of relational witnesses F_i, including direct comparisons F_i=F_j between witnesses of the same type. Assume C proves dependence of φ on finitely many named old-argument observations, finitely many comparisons F_i=C_r(c) of matching types, and finitely many mutual comparisons F_i=F_j. Add any missing same-type direct comparisons to the dependence premise; this strengthens that premise and remains a C-theorem.

For each witness type σ, let n_σ be its number of witnesses and k_σ the number of old entities of that type used in comparisons. Choose a common pool of L=max_σ(k_σ+n_σ) distinct false pure propositions q_l:=□Exactly_l(e). For each σ form the finite set of all identity tables on the UNION of the named observation tuples for witnesses of that type. The candidates for EACH σ-witness are all k_σ old entities C_r of that type and all translates of all those tables by K_σ(q_l).

Given a tuple F_i, partition the indices of each type by their ACTUAL identity. A class that is identical to an old C_r is assigned that C_r. For every remaining class, take a representative F and its truth table on the entire union of observations of this type. The L translates of this table have the required observations and are pairwise distinct. Choose one avoiding all k_σ old entities and all representatives already chosen for other unanchored classes of that type. There are at most k_σ+n_σ−1 forbidden values, fewer than L. Assign this same candidate to every member of the class.

The resulting old tuple has exactly the same complete direct identity pattern, including all identities to old entities, and the same specified observations. Its φ truth agrees by the dependence theorem. All choices range over a fixed finite candidate list; this is a finite C proof under G_q, not an invocation of a choice principle. The reverse implication is existential introduction. Accordingly the internal existential over the entire witness tuple reduces, under the same guard, to the finite disjunction over the Cartesian product of the candidate lists. Whole-guard equationalization and Boolean primeness give a permanent old witness tuple in every identity-correct quotient truth extending B.

For the E_1/global-coextension variant with first-order relational witnesses, replace every table list by the two constant relations. Actual identity classes have consistent truth bits on the sole individual tuple, and the same finite exclusion argument applies. Witnesses at different types are handled separately; no comparison of differently typed entities is introduced.

Sections 23 and 23.1 were independently audited by the sibling agent `/root/henkin_minimal` on 22 October 2026. Its audit checked the simultaneous identity patterns, anchored classes, duplicate old entities, nonempty-domain constant-lift injectivity, the exact finite pool bound, and whole-guard equationalization. This is an AI-agent mathematical audit, not human checking or Lean verification.

## 24. Finite entity-valued interpolation with direct identity exclusions

The parent proposed the following stronger finite graph construction. It deals with prescribed OLD output entities, so does not assume that arbitrary newly observed outputs are already available.

Fix an input type σ (possibly e) and a relational output type ρ. Let a_1,…,a_k be old entities of type σ and Y_1,…,Y_k old entities of type ρ. The necessary compatibility condition for a graph F(a_i)=Y_i is

    eq(a_i,a_j) ≤ eq(Y_i,Y_j)                    (all i,j).       (Compat)

This is stronger than saying actually equal inputs have equal outputs: it requires the identity proposition of the inputs to entail the identity proposition of their assigned outputs. It is necessary by the C identity-substitution inequality for application. It is also sufficient for the explicit old term

    T(x) := ∨_{i=1}^k [K_ρ(eq(x,a_i)) ∧ Y_i].

The empty join, when k=0, is bottom_ρ. Under Compat, T(a_i)=Y_i as ENTITY identities. Its i-th summand is Y_i. For every j, the compatibility inequality and gated identity substitution give

    K_ρ(eq(a_i,a_j))∧Y_j = K_ρ(eq(a_i,a_j))∧Y_i ≤ Y_i.

Thus all other summands are below Y_i, proving the claim. The gated substitution identity is a C consequence of Leibniz; the argument can be expressed as a guarded C theorem and holds in any quotient equipped with identity-correct truth when its Compat guard holds.

### 24.1 Nonzero perturbations vanishing at every prescribed input

Let r be the number of old forbidden functions C_1,…,C_r of type σρ. Choose r+1 pairwise different positive integers m_l with 2^{m_l}>k, and put

    b_l := B_(k+1,m_l),
    R(x) := ∧_{i=1}^k (x≠a_i),
    P_l(x) := K_ρ(b_l∧R(x)).

Each b_l is open, nonzero and different from top in B. It is actually false under identity-correct B truth. Different b_l have disjoint Boolean support, because their necessarily fixed proposition cardinalities differ. This use of finite S5 cells requires only their consistency, the boxed cardinality conjuncts and openness; it does not require their complete-theory or weak-atom results.

At a b_l point there are more than k entities of type σ. For σ=e the individual cardinality is k+1. For every relational σ, the constant-lift injection from t gives at least 2^{m_l}>k entities. Consequently C proves, uniformly in the finite tuple a_i,

    b_l ≤ ∃x^σ R(x).

One exact route is to prove in C the universally closed implication b_l→∃x R(x), using the finite pigeonhole argument; necessitate that WHOLE C theorem and use CBF to obtain the displayed necessary implication for every old tuple. No optional cardinality premise is separately necessitated.

Quantifier distributivity and nonempty output domains now give the proposition identity

    ∃x^σ ∃(output arguments of ρ) P_l(x)[output arguments] = b_l.

Thus P_l is a nonzero entity in every B-preserving quotient: if P_l were bottom, the left side would be bottom, contradicting the preserved b_l≠bottom. Also P_l∧P_j=bottom for l≠j, so these nonzero perturbations are pairwise distinct. Finally P_l(a_i)=bottom_ρ for every prescribed input, as a C identity, because one conjunct of R(a_i) is a_i≠a_i=bottom.

The old functions

    T_l := T Δ P_l

therefore still satisfy ALL prescribed entity equations T_l(a_i)=Y_i. They are pairwise distinct by Boolean cancellation. At most r of the r+1 candidates equal one of the r forbidden old functions, so at least one avoids them all. Moreover every T_l is actually coextensive with T at its full terminal relation type, because every b_l is actually false. No Functionality assumption identifies these coextensions.

### 24.2 Exact scope of the witness result

Accordingly every finite old entity-valued graph satisfying Compat has an old interpolant avoiding any specified finite list of old functions. For a quotient with identity-correct truth, a true internal existential assertion of the form

    ∃F [∧_i F(a_i)=Y_i ∧ ∧_{j=1}^r F≠C_j]

has a permanent old witness. Existential elimination in the guarded C proof first supplies Compat; the displayed finite candidate disjunction supplies an old T_l. Whole-guard equationalization applies exactly as in §23, using the finite true guard consisting of Compat and the required b_l nonzeroness/falsity facts. An injective later term map preserving old truth preserves that same witness.

This finite interpolation/avoidance theorem already holds in every genuine pure Max model. Its uses of the finite S5 cells are pure Max consequences and C equations; SP is not an additional hypothesis here.

The statement permits Boolean combinations of direct F=C_j tests by finite cases, including the old C_j themselves as candidates for equality branches. It also permits any additional property known by a C dependence theorem to be invariant under actual coextension with this particular interpolant, when that property is already true of T. It does NOT assert preservation of arbitrary observations whose output entities are genuinely new, nor of arbitrary structural or modal tests of F. Those would require further arguments.

## 25. Every actual Functionality class under SP has arbitrarily many entities

The uniform ghost construction has a quantitative extension. For every n≥1 put b_n=B_(n,2). The four-element proposition algebra at a b_n target has the same atom-swap ν as before. Extend it through the finite full hierarchy while acting IDENTICALLY on all n individuals. This is still a full logical-algebra automorphism and fixes every interpretation of the distinguished a. Consequently it fixes every pure a-term, just as in §19; the one-individual assumption was not needed for this particular action.

For every relational input σ, the same universal identity argument therefore gives

    SP ⊢ ∀X^σ [b_n≤(S_σX=X)]

for each fixed external n. For every relational output ρ the closed pure operators

    H_n(X) := K_ρ(b_n∧S_σX≠X)

are C-provably persistent, nonzero under Max, and have H_n(X)=bottom_ρ for every current X under SP. Different n give disjoint supports because the b_n require different necessarily fixed individual cardinalities. Thus the H_n are pairwise distinct nonzero entities.

For individual input σ=e, choose the current individual a and use instead, for n≥2,

    H_n(a)(x) := K_ρ(b_n∧x≠a).

These are pure a-terms, C-provably persistent and nonzero in B, as the finite b_n model with x≠a shows. SP's E_1 makes every current H_n(a)(x) literally bottom_ρ. Their dependence on a is essential: they are not counterexamples to the CLOSED pure single-individual-input theorem of §19.4.

It follows at every admitted operator type σρ that, for any current F and any fixed positive external integer N, SP has at least N pairwise distinct current operators that agree with F in their output ENTITIES at every current input. Take finitely many distinct ghost translates F Δ H_n (with a supplied in the individual-input case). Boolean cancellation makes them distinct, and their vanishing ghost values make each current output equal to F's. This asserts every finite multiplicity bound, not the existence of a coded internal infinite family or a choice principle.

Thus unrestricted Functionality fails with arbitrarily large finite multiplicity, even though each prescribed finite entity-valued input/output graph can be interpolated as in §24. The statement strengthens the explicit failures; it does not close the separate Henkin truth gap.

Sections 24 and 25 were independently audited by the sibling agent `/root/henkin_minimal` on 22 October 2026. The audit checked whole-theorem necessitation and CBF in the support calculation, entity-valued interpolation, literal vanishing at the prescribed inputs, the atom-swap fixing all n individuals, the required individual parameter in the e-input case, and the external-finite multiplicity qualification. This is an AI-agent mathematical audit only.
