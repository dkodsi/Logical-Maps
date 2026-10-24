# Symmetric surjection model with free-word gluing

22 October 2026. New construction and proofs by Codex, in ordinary ZFC and the original finitary relational language of C. No record or Lean edits; no human, independent, or formal verification is claimed. This is a second model, not a modification of the supported-product construction in `central-map.md`.

**Verified package.** For every permitted fixed set-sized Σ, this model satisfies Logical Necessity at the evaluation point, together with □Boolean Completeness, □BF, □Tame Rigidity, and □Weakly Rigid Power at all their admitted types, while satisfying Atomlessness and failing Actuality and Vicinity. It also fails Relational Choice. Consequently it strengthens the counterexample to Logical Necessity ⇒ Actuality, but is **not** a counterexample to Relational Choice + Boolean Completeness ⇒ Actuality. Arbitrary constant graph profiles are not admitted here.

Section 8 gives variants with the same positive package apart from BF, with an exact cancellation criterion deciding BF. Section 9 permits κ⁺ moving individuals and verifies the quantified infinity axioms while preserving the simultaneous interpretation of arbitrary fixed signatures.

## 1. Domains and closure

Choose an infinite κ≥|Σ|, a set U of cardinality κ⁺, and a free monoid W on κ generators. Let S be the monoid of all surjections U→U and let

    M=W×S,       (v,r)(w,s)=(vw,r∘s).

This is a one-object action category, evaluated at (ε,id). Its symmetry group is G={ε}×Sym(U). The typed individual domain is a singleton; U is the index set for pinning and symmetries, not the typed individual domain.

Recursively, a relational domain D_(σ̄t) contains exactly the profiles F:M→P(D_σ̄) satisfying both:

1. For some N⊆U, |N|≤κ, F_(w,s) depends only on w and s|N.
2. F_(w,πs)=π·F_(w,s) for every π∈Sym(U), acting on tuples through the lower-type actions.

Transport is `(h·F)_k=F_kh`. A transport by (w,s) changes a support N to s(N), still of size ≤κ. It preserves symmetry because left multiplication by a symmetry commutes with taking the profile's right translate. A symmetry is an invertible arrow and hence acts bijectively on each lower domain.

Application and λ-abstraction are the same flattened profile operations checked in `central-map.md` §1. Agreement on the external parameters' pinning sets makes their entire transports equal; quantification ranges over the same domains, so quantified abstraction preserves pinning. Symmetry is preserved by induction: the bijection π is an automorphism of the actual typed structure, since F_π=π·F_1, and therefore satisfaction with parameters π·ā and arguments b̄ equals satisfaction with ā and π⁻¹·b̄. This is precisely the symmetry condition for an abstraction. Boolean operations, identity and quantifiers obey the same argument. β and η are identities of complete profiles, as in the first note.

Literal entity equality is also correctly separated by Leibniz tests despite the absence of arbitrary constant graph profiles. For each entity a, its moving haecceity has profile m↦{m·a}. It is supported by a support of a and is symmetric by functoriality, hence admitted; its actual extension {a} separates a from any distinct entity. This argument also covers tuples and the singleton individual sort.

Thus the domains are closed under C's terms and validate H and Logical Equivalence with its original theoremhood proviso. Pure closed sentences have the same truth value at every arrow of this one-object model. All claims below using this fact concern pure sentences, not the signature schema Logical Necessity.

## 2. Boolean Completeness: a direct hull argument

Let A:τt be supported by N and put E=A_1. For any permutation π fixing N, pinning and symmetry give π·E=E. Define, for m=(w,s),

    J_(w,s) = ⋃ { a_(w,t) : a∈E, t∈S, t|N=s|N }.

This profile is N-supported. It is symmetric: replacing s by πs replaces each t by πt, and each a_(w,t) by π·a_(w,t). Thus J is admitted. It is an upper bound of E, taking t=s.

Let Z be any upper bound, supported by T. Suppose b̄∈a_(w,t), where a∈E and t|N=s|N. Let L support a. Choose a permutation π fixing N and moving L\N off T. This is possible because all prescribed sets have size ≤κ and |U|=κ⁺. Then π·a∈E.

Choose a surjection r agreeing with s on T and satisfying `(rπ)|L=t|L`. The prescriptions are compatible: any point of π(L)∩T lies in L∩N, where π is the identity and t=s. They prescribe at most κ arguments. Extend them to a surjection using the κ⁺ unprescribed arguments. Now

    b̄∈(π·a)_(w,r) ⊆ Z_(w,r)=Z_(w,s).

The first equality of relevant extensions uses pinning of a; the inclusion uses π·a∈E; the last equality uses pinning of Z. Hence J≤Z. This proves the least-upper-bound form of Boolean Completeness at every relational τ, with A's actual instances exactly as in the map. It is a pure closed schema, so □Boolean Completeness also holds.

This proof is the κ-pinning version of the symmetry/hull mechanism recorded for Dorr's ideally full models. It has been given directly here: no generalization from finite pinning is being assumed without verification, and the free word w remains the same throughout the splicing argument.

## 3. BF and simultaneous fixed-signature gluing

Every arrow acts surjectively on every typed domain. At e this is trivial. If a relational F has support N and s∈S, choose a permutation π of U with `(sπ)|N=id|N`: choose distinct preimages of the members of N under s, then extend that partial bijection to a permutation. Then s·(π·F)=F.

For the word factor v∈W, define L_v(F)_(w,s)=F_(u,s) when w=uv, and ∅ when w has no suffix v. Right cancellation of free words makes this well defined. It preserves F's support and symmetry, and v·L_v(F)=F. Composing these two surjectivity facts handles every (v,s). The usual direct argument gives BF at every type: a fresh target witness has a current preimage. Pure-sentence invariance gives □BF.

There are at most κ finitary Σ-sentences. Enumerate those satisfiable over this fixed pure model, and choose one full Σ-interpretation J_α for each. For each relational c, glue its chosen values along distinct final-letter sites:

    G_c(w,s)=J_α(c)_(u,s) if w=u f_α,
             ∅ otherwise.

Its support is the union of at most κ supports, hence has size ≤κ. Symmetry is preserved because it changes only s, not the free-word suffix. At h_α=(f_α,id), h_α·G_c=J_α(c), simultaneously for every relational c. Individual constants all denote the unique individual. This covers all the constants of the prescribed Σ, including individual constants, and never assumes that distinct symbols have distinct denotations.

Thus ◇φ holds in the glued expansion iff φ is satisfiable over the fixed pure model. For pure P with free variables among a finite tuple x̄ matching distinct constants c̄, this gives

    ◇P[c̄/x̄] ↔ ∃x̄ P,

and by negation the map's Logical Necessity schema. Empty tuples are covered. Logical Necessity is asserted only at the evaluation point. Its boxed form is not inferred from one-object pure-sentence invariance.

## 4. Atomlessness, Actuality and Vicinity

For distinct a,b∈U, let q_(a,b) be the proposition that s(a)≠s(b); it ignores the word coordinate. It is symmetric and supported by {a,b}. Given any nonzero p with support N, choose a,b outside N. At a member (w,s) of p, the partial prescription s|N extends to surjections making a,b equal or unequal. Thus both p∧q_(a,b) and p∧¬q_(a,b) are nonzero. This proves Atomlessness, hence failure of Actuality.

The same argument proves atomlessness of the Boolean algebra at **every relational type**. Given a nonzero F, choose a tuple in one of its extensions and a,b outside a support of F. The two altered surjections keep that same tuple in F while giving opposite truth values to q_(a,b). The pointwise relations F∧q_(a,b) and F∧¬q_(a,b) are therefore nonzero complementary parts of F. This strengthens the named propositional Atomlessness verdict without adding a new principle to the database.

For Vicinity, let p be true and supported by N. Choose a,b outside N and a surjection s fixing N but collapsing a,b. Then p holds at (ε,s), while the true proposition q_(a,b) is impossible there: every later composition preserves that collapse. Consequently no truth entails the possibility of every truth. These pure failures hold at every arrow.

## 5. Exact images and Tame Rigidity

For an external set E of tuples put H_E(m)=m·E. A weakly rigid, N-supported Y with Y_1=E is exactly H_E. For the proof define

    B_N(E)_(w,s)=⋃{(w,t)·E:t|N=s|N}.

This is admitted: pinning is immediate, and its symmetry follows from functoriality of the action. It necessarily contains every actual E-member, so weak inextensibility gives Y≤B_N(E). Weak persistence gives m·E⊆Y_m.

For b̄∈Y_(w,s), choose ā∈E and t agreeing with s on N such that b̄=(w,t)·ā. Let L support ā. Since s is onto, prescribe a surjection u fixing N with `(su)|L=t|L`; the prescriptions are consistent on L∩N and extend to a surjection outside their ≤κ-sized domain. Weak persistence and pinning give u·ā∈E. Hence b̄=(w,s)·(u·ā) belongs to (w,s)·E, proving equality.

Conversely every admitted H_E is rigid: it has exact transported extensions, so every necessary cover of its actual instances covers the whole profile; the same argument applies to every transport. Thus weak rigidity equals rigidity, and all-type □Tame Rigidity follows.

## 6. Rigid Power and Weakly Rigid Power

We first need a stability lemma. If A is closed under every (ε,u) with u surjective and fixing P pointwise, |P|≤κ, then H_A is P-supported and hence admitted and rigid. Indeed, for s|P=t|P and ā∈A supported by L, prescribe a surjection u fixing P with `(su)|L=t|L`. Then `(w,t)·ā=(w,s)·(u·ā)∈(w,s)·A`. Reversing s,t proves equal images. Symmetry of H_A is automatic from functoriality. Notice that neither a bound on |A| nor a free-word restriction on its elements is needed.

Let F=H_E be rigid and supported by S. To test weak inextensibility of its power property P_F, take an admitted Z necessarily holding of all actual rigid subrelations of F. Let N contain S and a support of Z. Fix h=(w,s) and a rigid X=H_D≤h·F, supported by T.

Choose a surjection j₀ agreeing with s on N and mapping U\N bijectively onto U\s(N). All nonsingleton fibres of j₀ are contained in N. Put j=(w,j₀). Then j·F=h·F and D⊆j·E. Let

    P=N∪j₀⁻¹(T),        A={ā∈E:j·ā∈D}.

The set P has size ≤κ: fibres over j₀(N) lie in N, and all other fibres are singletons. If u is a surjection fixing P, then j₀u is constant on every fibre of j₀. Hence j₀u=vj₀ for a surjection v fixing T. Since F and X are weakly persistent and u fixes S while v fixes T, we have u·E⊆E and v·D⊆D. Consequently u·A⊆A, because j·(u·ā)=v·(j·ā).

By the stability lemma Y=H_A is admitted and rigid, Y≤F, and j·A=D. Thus j·Y=X. The assumed necessary cover gives X∈Z_j. Since j and h have the same word and agree on N, Z_j=Z_h. We have proved every member of P_F at every h belongs to Z_h. Thus P_F is weakly inextensible. Its persistence is the ordinary C fact that rigidity and entailment persist. Tame Rigidity now makes P_F rigid.

This proves all-type Rigid Power, and the pure one-object argument boxes it. Global Tame Rigidity identifies weakly rigid subrelations with rigid subrelations at every point, so the same power properties give Weakly Rigid Power and its box. This extends the strategy of the recorded `rigid-power-surjections` argument; the proof above explicitly checks that retaining the same free-word coordinate makes all its steps valid here.

## 7. Why this does not settle Relational Choice + BC ⇒ Actuality

Unlike the first supported-product model, this one does not admit every constant extension profile. A constant profile with extension E must satisfy π·E=E for every symmetry π. External selection does not ensure that condition.

In fact Relational Choice fails, even with the typed individual domain a singleton. Consider the pure serial relation that, given a property A:tt having exactly two propositional members, permits precisely those members as outputs; for other A it permits any proposition. Suppose an admitted functional subrelation R existed and let N support R. Choose distinct a,b,c∈U\N. Let p₁=q_(c,a), p₂=q_(c,b); these are distinct, as witnessed by a surjection collapsing c,a but not b. Let A be the finite union of their haecceities, so its actual members are exactly p₁,p₂.

The permutation π exchanging a,b and fixing c and N swaps p₁,p₂ and fixes A. Pinning gives π·R=R, and symmetry makes its actual extension invariant under simultaneous application of π to its arguments. Thus a selected output for A is accompanied by the other output, contradicting functionality. This refutes the Relational Choice instance with input type tt and output type t. No e-valued function type is used.

For contrast, the first model in `central-map.md` does admit every constant graph profile, so external ZFC selection proves Relational Choice there; that model fails full Boolean Completeness. Neither construction supplies Relational Choice + Boolean Completeness + ¬Actuality. This distinction was checked explicitly in response to the new question.

A later direct [support audit](choice-support-obstruction.md) sharpens this verdict to RC_(t,t): the explicit serial relation selecting a false proposition outside each proper upper bound has no admitted functional subrelation. The proof identifies local truth atoms for support fragments and shows that any admitted total subrelation must have a fibre larger than κ at an input determined by its support. This is a structural obstruction, not an inference from the absence of a constant graph.

## 8. The first monoid factor controls BF independently

There is a useful generalization of the construction. Replace W by any set-sized monoid K, leaving the pinning and symmetry conditions unchanged and allowing profiles to depend arbitrarily on the whole K-coordinate. The closure, Boolean-completeness, exact-image, and power arguments in §§1–2 and 4–6 still apply: every splice keeps this coordinate fixed, and the auxiliary arrows have K-coordinate 1. Thus □Boolean Completeness, □Tame Rigidity, □Weakly Rigid Power, Atomlessness, and the failures of Actuality, Vicinity and Relational Choice hold for every K.

In this family, all-type BF holds **if and only if K is right cancellative**, meaning av=bv implies a=b. For the forward construction, right cancellation lets the word-preimage formula from §3 work verbatim: set L_v(F)_(k,s)=F_(u,s) when k=uv and empty otherwise. Uniqueness of u makes this well defined, with v·L_v(F)=F. Pinning and symmetry are preserved. Combined with the surjection-factor argument, every arrow acts onto every typed domain, so □BF follows.

Conversely, suppose av=bv with a≠b. Let p be the proposition whose K-coordinate is a, independent of its U-coordinate. Then p takes different values at a and b. Every transport along an arrow with K-coordinate v takes equal values there, so none can equal p. The admitted predicate R:tt whose extension is {p} precisely at K-coordinate v and empty elsewhere satisfies ◇∃q Rq but not ∃q◇Rq. Thus already BF_t fails. This uses only profiles with empty U-support, so no extra pinning or symmetry assumption is hidden in the criterion.

Logical Necessity can still be obtained whenever K=W×J for an arbitrary set-sized monoid J: glue at (f_α,1_J), stripping the last free letter and retaining the J-coordinate. The same support-union argument works. Consequently these factors give the preceding full package with Logical Necessity, while BF holds exactly when J is right cancellative. The necessity direction follows by taking free-word coordinate ε; the sufficiency direction follows because products of right-cancellative monoids are right cancellative.

### The two-element example

The closure, Boolean-completeness, exact-image, and power proofs do not use cancellation in the word coordinate: they keep that coordinate fixed when splicing surjections. Replace W by V=W×{1,d}, where d²=d≠1, and let the support condition remember the whole V-coordinate. All those proofs remain unchanged. Gluing still works at the sites (f_α,1), stripping the final free letter and retaining the idempotent coordinate. Thus this separate variant preserves Logical Necessity, □Boolean Completeness, □Tame Rigidity, □Weakly Rigid Power, Atomlessness, and the failures of Actuality, Vicinity and Relational Choice.

BF_t now fails. Let p be the admitted proposition that the V-coordinate is 1_V; it ignores the surjection coordinate and is fixed by every symmetry. No transport along an arrow with V-coordinate d₀:=(ε,d) can equal p: its values at V-coordinates 1_V and d₀ are equal, since 1_Vd₀=d₀d₀, whereas p's values differ. Let R:tt have extension {p} exactly at arrows whose V-coordinate is d₀, and empty extension elsewhere. It is symmetric and needs no U-support. Then ◇∃q Rq holds, but no current q has ◇Rq, because at every possible witness arrow its transport would have to equal p. This directly refutes the dual BF_t instance. The primary free-word model's positive □BF verdict is unchanged; this paragraph defines a different model.

## 9. Moving individuals: the same result with actual infinity

The singleton individual domain is not essential. In a further variant take D_e=U and let (k,s) send a∈U to s(a); the K-factor acts trivially on individuals. Give each individual a the singleton support {a}. Keep precisely the same recursive profile, support, and symmetry definitions at relational types, now using these lower-type actions. This is a change of model, not a change to the primary model in §1.

The closure proof still works: each individual parameter has a support, transport changes its support to its image, and permutations are bijections of D_e. Haecceities m↦{m·a} are admitted as before. Every proof of BC, exact images, Tame Rigidity, Rigid Power, and failure of Relational Choice uses only supports of finitely many tuple entries, so their proofs are unchanged. The surjection-factor action is onto at e by definition and onto at relational types by the permutation-preimage argument of §3. The BF criterion of §8 therefore holds here too. Atomlessness and the failure of Vicinity use the same propositional profiles q_(a,b); they do not depend on the old choice of D_e.

In this variant Relational Choice already fails with input type et and output type e. A serial relation can require a member of each two-element individual property, allowing any output otherwise. If a selecting graph had support N, choose a,b outside N. Their two-element haecceity property is fixed by the permutation swapping a,b, as is the graph; that permutation exchanges the only permitted outputs. Functionality is impossible. This uses the same symmetry obstruction as §7 at lower types.

There is an additional step in gluing individual constants. Work with K=W×J, allowing J to be the trivial or the two-element monoid from §8. Enumerate the satisfiable Σ-sentences and choose their full witness interpretations J_α over this new pure model. Choose pairwise distinct a_c∈U for all individual constants c of Σ. For each α choose a surjection s_α satisfying

    s_α(a_c)=J_α(c)    for every individual constant c.

There are at most κ prescriptions on distinct arguments, and the complement has size κ⁺, so they extend to a surjection even when the desired values coincide. For every relational constant c choose a profile B_(α,c) with s_α·B_(α,c)=J_α(c). Such a preimage exists by the preceding surjection-factor argument, independently of any cancellation in J.

Interpret each individual c by a_c. Interpret each relational c by gluing B_(α,c) along the final free letter f_α, exactly as in §3, retaining the whole J-coordinate. At

    h_α=(f_α,1_J,s_α)

every constant, of either kind, now transports to its J_α-value. For a relational c, at a test coordinate (u,j,r) this equality reads

    (h_α·G_c)_(u,j,r)
      = B_(α,c)_(u,j,r s_α)
      = J_α(c)_(u,j,r).

The support of each glued profile is still a union of at most κ supports. Thus the same satisfiability argument proves the full fixed-signature Logical Necessity schema, including arbitrary individual constants. No typed e-valued functions are introduced: the surjections are external arrows of the model.

This variant also satisfies the map's quantified **Axiom of Infinity at e**, not merely its finite infinity schema. Here is the internal-cardinality check. Let O_σ={Suc_σⁿ(0_σ):n∈N} be the external orbit of the pure cardinality terms at any type σ. Every such term is fixed by every arrow in the one-object model. Consequently the constant profile with extension O_σ is symmetric, empty-supported, and admitted. It is an inductive property, while external finite induction shows that every actual inductive property contains O_σ. Therefore the actual FiniteCardinality_σ-extension is exactly O_σ. Induction on the external n shows that its nth member holds of a property precisely when that property's actual extension has n elements. Since D_e=U is infinite, none holds of the universal individual property, which proves the quantified axiom. The same reasoning at t proves its Axiom of Infinity, using the infinitely many distinct propositions supplied by Atomlessness. These are pure truths, hence necessary in this model.

Accordingly the counterexample with Logical Necessity, □BC and □Weakly Rigid Power can have κ⁺ individuals and the quantified infinity axioms. It remains a failure of Relational Choice, so this strengthening does not answer the Choice + BC question.

## 10. Status and source boundary

The model is an ordinary proof construction, not an engine-generated model entry. A proved-only compatibility query found no conflict for the primary package including Logical Necessity, □Boolean Completeness, □BF, □Tame Rigidity, □Weakly Rigid Power, Atomlessness, and the failures of Actuality, Vicinity and Relational Choice. A separate query found no conflict for the noncancellative variant with BF_t among the failures and the other stated positive properties retained. Those are checks against existing rules, not substitutes for the proofs above. No ranking recomputation or literature-novelty claim is made. The original pinned models' Rigid Power verdicts remain unchanged.

Further proved-only checks also found no conflict after adjoining the quantified infinity axioms at e and t to the moving-individual versions, both with □BF and with failure of BF_t. The new §9 gluing step was checked by direct calculation at an arbitrary test coordinate; the arithmetic paragraph separately checks the actual impredicative FiniteCardinality definition. These remain self-audits, not independent certification.

Neither variant settles Maximalism + Weakly Rigid Power. They have No Pure Contingency and fail Actuality everywhere, so ◇Actuality is false, whereas pure Maximalism requires it because Actuality is consistent with C. Replacing Logical Necessity with Maximalism would therefore need a different construction, not a reinterpretation of these constants.

Background sources are Bacon–Dorr, *Classicism*, draft 16 May 2023, §3.5 pp.58–61 and Appendix D pp.73–79; Dorr, *Boolean Completeness does not imply Rigid Comprehension*, draft 30 July 2026, Definitions 15–18 and Theorem 36 pp.18–19, as transcribed in `groups/symmetric-ideally-full.yaml`; and Bacon's gluing construction recorded in the local free-monoid write-up. The larger pinning bound, added free-word factor, and verifications in this note are new arguments with direct source `misc` if integrated. They are not attributed to those sources. The frozen archive remains untouched.
