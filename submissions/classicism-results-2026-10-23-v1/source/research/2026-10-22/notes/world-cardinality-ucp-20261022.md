# Universal rigid-profile realization and a Boolean algebra of worlds

Original research notes, 22 October 2026. Ordinary mathematical arguments; no Lean work, database edits, or literature-novelty claim. Results below have been developed by the world-cardinality research agent and require the parent researcher's audit before recording. The fixed framework throughout is C, in its relational type system. No function type with output e is used.

**Principal direct Maximalism obstruction (§32; independently checked by the parent lane):** Pure Maximalism proves, for every V^{et} and a^e,

    ¬[Atom(∀x ¬Vx) ∧ Atom(∀x(Vx↔x=a))].

At a monist possibility V must match one of these two profiles, whereas Maximalism makes the monism proposition contain three pairwise disjoint nonzero subpropositions. This refutes the original AUCP_e without Atomicity, Choice, BF, ND or actual monism. Raw UWR has a different status outside B; see §§17 and 31. The broader structural and Infinity results, including the countable-independence and compactness characterizations, are in §§20–30.

## 1. Standing premises and recorded dependencies

Write B for C + □Plenitude, and F for C + □Functional Choice. The recorded equivalence B = C + □ND + Atomicity is used, not unboxed ND + Atomicity. F implies B.

The proved-only Engine, with optional hypotheses in the queried premise set, confirms that B entails □BF, □Rigid Comprehension, □Boolean Completeness, □Actuality, and Strong Leibniz. Relevant records include `c5-and-atomicity-imply-necessary-plenitude`, `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`, `necessary-distinctness-necessary-r-implies-necessary-barcan-r`, `c5-and-atomicity-imply-necessary-rigid-comprehension`, and `c5-and-atomicity-imply-necessary-completeness`. Their direct source is Bacon–Dorr, Classicism, draft 16 May 2023, §§2.1–2.3, pp. 21–34. Full action models are from §3.5, pp. 58–61, and Appendix D, pp. 73–74. These are background sources, not attribution for the new arguments below.

All equality claims between predicates below use C's Intensionality (necessarily coextensive relations are identical), or the established C lemma that coextensive rigid predicates are identical. They do not apply the Logical Equivalence schema to equivalences proved from optional assumptions.

Useful B lemmas:

1. Every equality or inequality of objects is settled, by NI and □ND. With □BF, quantified combinations of settled formulas are settled too.
2. A predicate whose positive and negative instances are necessarily preserved is rigid. For inextensibility, if every actual R-instance necessarily satisfies Y, then every actual x necessarily satisfies R(x)→Y(x), including the noninstances, and BF gives the required necessarily universal inclusion. The same proof holds at every world.
3. Thus predicates built from identities, inequalities and their quantifications are rigid. Atom(a), order a≤b, and the profiles used below have this property.
4. If X is rigid, each Xx is settled. Persistence gives the forward direction; S5 plus necessary persistence gives the reverse direction.

## 2. Proposed principles

For an admitted type σ, a candidate V of type σt, and X of type σt, put

    q_X(V) := ∀x^σ (Vx ↔ Xx).

Universal rigid-profile realization at σ is

    UCP_σ := ∃V^{σt} ∀X^{σt} (Rigid(X) → ◇q_X(V)).

The unique-atomic version is

    AUCP_σ := ∃V^{σt} ∀X^{σt} (Rigid(X) → Atom_t(q_X(V))).

Names are proposals only. AUCP implies UCP. The universal quantifier concerns rigid profiles; replacing it by all profiles is immediately contradictory by X=¬V. These are entirely formulas of C, with no infinitary syntax.

## 3. Why e is the unique viable unrestricted input type

**Theorem 1.** B refutes UCP_τ at every relational type τ, including t.

First let τ=t and fix V^{tt}. Define

    X(p) := Atom_t(p) ∧ (p ≤ ¬Vp).

The B lemmas show that X is rigid: all its conditions are settled. At any accessible world there is a true atom w, by □Actuality. A true atom entails precisely the true propositions there, so

    Xw ↔ (w≤¬Vw) ↔ ¬Vw.

Consequently V and X cannot be coextensive at that world. Since the world was arbitrary, □¬q_X(V), contradicting the UCP requirement.

For τ=σ₁…σₙt, define the constant-relation embedding k:t→τ by k(p)=λy₁…yₙ.p. It is injective because every argument type is inhabited, and equality of the constant relations entails equality on an argument tuple. Put

    X(z) := ∃p (Atom_t(p) ∧ z=k(p) ∧ p≤¬Vz).

Again X is rigid. At any world take its true atom w and z=k(w). Injectivity of k makes Xz equivalent to w≤¬Vz, hence to ¬Vz. This proves the contradiction. No forbidden output-e function is involved.

**Theorem 2.** More generally, B + UCP_σ refutes any relational injection of the atoms into σ.

Suppose J(a,x) assigns each atom at least one x and no x is assigned to two different atoms. Define a rigid X coextensive with

    x ↦ ∃a (Atom(a) ∧ J(a,x) ∧ ¬(a≤Vx)).

Rigid Comprehension supplies X; J need not itself be rigid. UCP supplies a possible q_X; choose an atom a≤q_X and an x with J(a,x). At the actual point, uniqueness of a at x gives Xx↔¬(a≤Vx). But a≤q_X and settledness of Xx imply a≤Vx iff Xx, contradiction. This is a proof at the actual point, so no transport of the possibly nonrigid J is assumed. Multiple codes per atom are harmless.

## 4. Full S5 models and strictness

For any nonempty set D and nonempty world set W, take the full S5 model with constant individual domain D and exactly one arrow between every pair of worlds. It satisfies B; in ordinary ZFC it satisfies □Functional Choice. The full model with these parameters is a direct instance of the recorded full-action construction, not a newly assumed semantics.

Rigid e-properties are exactly constant subsets of D. A candidate V is equivalently a map h:W→P(D), where h(w)={d:Vd is true at w}. Then:

* UCP_e holds exactly when some such h is surjective.
* AUCP_e holds exactly when some such h is bijective.

These are exact model calibrations, not claims that every Henkin model has external full powersets.

For W=P(D), use h(S)=S, or V(d)={S⊆D:d∈S}. This gives AUCP_e and hence UCP_e. Thus both are consistent with F and any chosen finite or infinite D. For D=ℕ it gives an elegant model with infinitely many individuals and worlds realizing exactly all their binary profiles.

One-world full models satisfy F but refute UCP_e, since both the empty and universal rigid profiles would have to be realized and D is nonempty. Thus UCP_e and AUCP_e are genuine strict strengthenings of F, relative to the usual set-theoretic model existence.

AUCP_e is strictly stronger than UCP_e even with infinitely many individuals. Take D=ℕ and W=P(P(ℕ)). A surjection h:W→P(ℕ) is h({S})=S, with h(A)=∅ on nonsingletons. This witnesses UCP. AUCP would require an injection P(P(ℕ))→P(ℕ), contradicted by Cantor. This strictness does not rely on CH or an unproved cardinal inequality. Duplicating every world only twice would not establish the infinite strictness, since an alternative profile map can still be bijective.

## 5. Finite calibration

Over B plus the assertion of exactly m≥1 individuals:

    UCP_e  iff  there are at least 2^m propositional atoms;
    AUCP_e iff  there are exactly 2^m propositional atoms.

Enumerate the individuals a₁,…,a_m. BF and NI make that enumeration exhaustive necessarily. The rigid profiles are exactly the 2^m subsets S of this list. For a candidate V, their propositions are the Boolean cells

    q_S = ∧_{i∈S} Va_i ∧ ∧_{i∉S} ¬Va_i.

They are pairwise disjoint and their finite join is top. UCP makes each nonzero; Atomicity then supplies distinct atoms below them. AUCP makes precisely those cells the atoms, exhausting all atoms.

Conversely choose distinct atoms a_S for each subset S and define the m coordinate propositions p_i=∨_{S∋i}a_S. Let V be the individual predicate with these coordinate values. Every a_S realizes profile S. Unused atoms, if any, go into the all-false cell. If the listed atoms exhaust all atoms, Atomicity ensures their join is top, so each cell is exactly its assigned atom. Only finite selection is used.

In particular UCP_e with one individual amounts to a contingent proposition; AUCP_e with one individual requires exactly two world atoms. Neither axiom by itself forces infinity.

## 6. Internal bijection under AUCP

Fix an AUCP witness V. The map X↦q_X is an internal bijection between rigid e-properties and propositional atoms.

For surjectivity, let a be an atom and define

    X_a(x) := a≤Vx.

This is rigid by the B lemmas. The atom a decides each Vx. Because X_a(x) is settled, a≤(Vx↔X_a(x)) for every actual x. BF combines these into a≤q_{X_a}. The latter is an atom, so a=q_{X_a}.

For injectivity, if q_X=q_Y=a, then a≤q_X∧q_Y. If X and Y disagreed on an actual x, their settledness would make a entail contradictory truth values at x. Thus X and Y are coextensive, and their rigidity gives X=Y. The displayed map is an admitted λ-term of type (et)t; no choice is needed.

Conversely, any internal bijection f from rigid e-properties onto atoms yields an AUCP witness. For each x take the Boolean join of the atoms f(X) for rigid X with Xx. Its uniqueness and Plenitude produce a predicate V assigning those joins. The atom-join lemma in §8 shows f(X)≤Vx iff Xx. Hence f(X)≤q_X. No other atom lies under q_X, because every atom is f(Y) and its profile recovers Y. Atomicity then gives q_X=f(X).

## 7. Choice, UCP, and strict cardinal inequalities

Under F, UCP_e is equivalent to the existence of an internal injection from rigid e-properties into atoms. Forward: each q_X is nonzero; Functional Choice selects an atom f(X)≤q_X, with a fixed default for nonrigid X. Distinct profiles have disjoint q's, so this choice is injective on rigid profiles. Reverse: given an injection f, use the Boolean joins from §6 to construct V. Extra atoms may be left in the all-false profile, so surjectivity of f is unnecessary.

Under AUCP, the singleton profile H_x(y):=(y=x) gives a definable injection

    x ↦ q_{H_x}

from individuals to atoms. Under mere UCP, Functional Choice selects atoms below these pairwise disjoint nonzero propositions, giving an injection too. Theorem 2 forbids any injection back. The atoms themselves embed into propositions by inclusion. Theorem 3 below forbids an injection back. Thus F+UCP has the strict internal cardinal chain

    individuals < propositional atoms < propositions.

Here '<' means an admitted relational injection in the forward direction and no admitted relational injection in the reverse direction. It is not an assertion about external cardinalities in arbitrary Henkin models.

## 8. A choice-free Cantor theorem for atoms

**Theorem 3.** C + Boolean Completeness at t refutes every total atom-coding relation for all propositions whose code fibers are pairwise disjoint. In particular it refutes an injection from propositions to atoms. Atomicity, Choice and Plenitude are not needed.

Suppose R(p,a) gives every proposition p at least one atom a, and no atom a codes two different propositions. Define

    S(a) := Atom(a) ∧ ∃p(R(p,a) ∧ ¬(a≤p)).

Let d be its join, supplied by Boolean Completeness. For every atom a,

    a≤d iff S(a).

The reverse implication is the upper-bound property. For the forward implication, if ¬S(a), every b with S(b) is a distinct atom, hence b≤¬a. Thus d≤¬a; since a is nonzero, a≤d would be impossible.

Choose an atom a with R(d,a). The condition R(p,a)∧R(q,a)→p=q makes S(a) equivalent to ¬(a≤d), contradicting the displayed equivalence. Allowing multiple disjoint atom codes for each proposition does not avoid this diagonal.

## 9. A Boolean group of worlds

Under AUCP fix V and identify each atom with its unique rigid profile. For atoms a,b define a⋆b to be the unique atom c whose profile is the coordinatewise exclusive-or:

    c≤Vx iff ((a≤Vx) xor (b≤Vx)), for every x.

Existence follows by applying AUCP to the rigid predicate on the right; uniqueness follows from §6. Extend the rule by a fixed atom on nonatom inputs. Its graph is total and single-valued, so polyadic Plenitude represents it by an operation of type ttt, which is admitted.

The all-false-profile atom 0_A=q_∅ is the identity. Exclusive-or of profiles proves associativity and commutativity, and a⋆a=0_A. Equality of profiles implies equality of atoms by §6, so these are equations of objects, not merely coextension assertions. Thus the atoms form an elementary abelian 2-group.

For each individual x, let s_x=q_{H_x}. Translation a↦a⋆s_x is a fixed-point-free involution which flips exactly the x-coordinate. Distinct coordinate flips commute. For m distinct individuals, the 2^m finite products are distinct, as evaluation of coordinates shows. More generally every rigid individual subset X determines the translation by q_X, toggling exactly X. This group acts regularly on its atoms; the all-false world supplies a canonical origin relative to V.

No external choice is required for these constructions under AUCP. The entire group is internal to the relational types already available in C.

## 10. Finite-pattern realization is weaker

The schema that every binary assignment on n distinct individuals is possible, for each external finite n, is weaker than UCP_e, even with infinitely many individuals and F.

Take full S5 with D=ℕ, W=[ℕ]^{<ω}, and V(n) true at finite S iff n∈S. Every finite prescribed pattern is realized, but no V can realize every subset of ℕ: W is countable and P(ℕ) is not. Thus the existential full UCP principle fails, not merely this particular V. This argument uses the ordinary ZFC model calibration. No claim here identifies a finite schema with the impredicative Frege Axiom of Infinity.

## 11. Strong Possibility/cardinality side results

These are separate from the UCP package and do not assume B.

**Theorem 4 (C's relational Cantor diagonal).** C forbids a relation R from all σ-properties to σ with nonempty pairwise disjoint code fibers: ∀Y∃x R(Y,x) and R(Y,x)∧R(Z,x)→Y=Z. Multiple codes for each property are allowed. Define D(x):=∃Y(R(Y,x)∧¬Yx). Choose x with R(D,x). The disjoint-fiber condition yields D(x) iff ¬D(x), contradiction. The λ-term D is admitted even at σ=e.

The recorded theorem `pure-possibility-implies-axiom-of-infinity-t`, proof §4, Lemma 6, supplies under Max(C) an injection g from Frege natural cardinalities N_e into propositions, g(Z):=Suc_e(Z)(⊤_e). Consequently Max(C) refutes `Ctbl_{e,tt}(⊤_{tt})` in the exact background convention. A purported countability relation for all properties of propositions, composed with g, is a total relation from tt into t with disjoint nonempty code fibers; Theorem 4 refutes it. No Choice is needed. This does not refute internally countably many propositions, nor externally countable Henkin models. It is a higher-type obstruction only. The fact that Strong Possibility forces one actual individual does not truncate N_e: larger cardinalities can remain distinct because they are possibly instantiated, as the recorded Π proof ensures.

**Theorem 5.** Strong Possibility (pure) refutes unboxed Functionality already at e→t, and hence refutes BF at e.

The recorded monism theorem gives a sole actual individual a; Strong Possibility entails Max(C), which gives the possibility of exactly two individuals. Let H=λx(x=a) and T=λx⊤. Every actual x equals a, and NI makes Hx=⊤=Tx. Yet H=T would imply □∀x(x=a), contradicting possible two individuals. Therefore all actual outputs agree while H≠T. More generally Max(C) plus any fixed finite actual individual bound refutes Functionality at e→t, using the characteristic predicate of the finite actual list. No forbidden e→e type is used.

Source caveats: The monism and Maximalism consequences in this section are recorded human or previously recorded arguments. The Cantor applications and Functionality corollary here are new deductions, not claims made by their cited background sources. Strong Possibility's consistency remains unresolved by these notes.

## 12. Improved formulations: world representation

The parent researcher supplied the following substantially cleaner equivalent definitions. The original UCP/AUCP formulations above are preserved to make the equivalence and its assumptions explicit.

    WR_σ := ∃V^{σt} ∀X^{σt} ∃w^t
              (Atom(w) ∧ ∀x^σ (Xx ↔ w≤Vx)).

    UWR_σ := ∃V^{σt} ∀X^{σt} ∃!w^t
              (Atom(w) ∧ ∀x^σ (Xx ↔ w≤Vx)).

Thus every actual extension of a predicate is represented by a world; in UWR it has exactly one representing world. Arbitrary X are allowed, because only their actual extensions enter the clause. There is no need to introduce rigid profiles or an explicit possibility operator in the displayed axiom.

**Theorem 6.** Over B, WR_σ is equivalent to UCP_σ, and UWR_σ to AUCP_σ, with the same V as witness.

From UCP, rigidify the given actual predicate X to Y. There is an atom w≤q_Y. For each x, since Yx is settled and w nonzero, w≤Vx iff Yx iff Xx. This proves WR. Under AUCP the representing world is q_Y. Any other representing atom a satisfies a≤q_Y by the converse argument next, hence a=q_Y, proving uniqueness.

Conversely, apply WR to a rigid X, obtaining w. If Xx, settledness gives w≤Xx, and the representation condition gives w≤Vx. If ¬Xx, settledness gives w≤¬Xx, while atom dichotomy and ¬(w≤Vx) give w≤¬Vx. Thus w≤(Vx↔Xx) for every actual x. BF gives w≤q_X, making q_X nonzero. This proves UCP. If the representation is unique and q_X were not an atom, Boolean algebra plus Atomicity would give two different atoms below it. Both would represent X by the forward argument, contradiction. Thus UWR proves AUCP.

**Theorem 7.** C alone refutes WR_σ at every relational type σ. This strengthens the assumptions in the original Theorem 1 when the principle is written as WR.

At σ=t, fix V and take X(p):=¬(p≤Vp). A representing w would yield, on instantiating at p=w,

    ¬(w≤Vw) iff w≤Vw,

an outright contradiction. The atom condition is not even needed in this diagonal.

At σ=σ₁…σₙt use the injective constant-relation map k:t→σ and put

    X(z):=∃p(z=k(p) ∧ ¬(p≤Vz)).

A representing w, tested at z=k(w), gives the same contradiction. This uses only comprehension, equality and inhabited argument types, all in C. It does not presuppose S5, BF, rigidity or a cardinal model.

**World separation.** For a fixed V define

    Sep(V):=∀a,b (Atom(a)∧Atom(b)∧
               ∀x(a≤Vx↔b≤Vx) → a=b).

Over B, AUCP(V) is equivalent to UCP(V)∧Sep(V). Equivalently, UWR(V) is WR(V)∧Sep(V). The latter equivalence is immediate by applying WR to the profile x↦a≤Vx. This decomposes the principle into two clear commitments: every profile is realized, and profiles determine worlds.

The same-witness proviso matters. From ∃V UCP(V) and ∃V Sep(V), one cannot merely conjoin the witnesses. Under Functional Choice an internal Cantor–Schröder–Bernstein argument can instead supply a bijection and then AUCP.

**Cardinal formulations and exact assumptions.** Over B, without Choice:

* WR is equivalent to an internal surjection from atoms onto rigid σ-properties.
* The existence of a separating V is equivalent to an internal injection from atoms into rigid σ-properties.
* UWR is equivalent to an internal bijection between these two domains.

For the forward maps, send an atom a to the unique rigid coextension of x↦a≤Vx; uniqueness plus Plenitude represents this operation. WR gives surjectivity, and separation gives injectivity. Conversely, given a map f from atoms to rigid σ-properties, set Vx to the join of the atoms a such that (fa)x, using Boolean Completeness and Plenitude. The atom-join lemma shows that its world profiles are exactly f. These arguments give all three equivalences. Choice is needed only to replace the surjection formulation of WR by an injection in the reverse direction, as in §7.

## 13. The worlds themselves form a complete atomic Boolean algebra

The Boolean group in §9 is part of a stronger structure. Under UWR_e, put A=Atoms(t) and define, for a,b∈A,

    a ≼ b iff ∀x(a≤Vx → b≤Vx).

This order is not the original propositional order ≤, under which distinct atoms are incomparable. It is inclusion of individual profiles. Likewise the operations below are new operations on worlds, not the original propositional operations.

UWR supplies worlds for the empty and universal profiles, denoted 0_W and 1_W. They are genuine nonzero propositions, even though they serve as bottom and top in the new algebra. The representing worlds for profile union, intersection and complement give the Boolean operations ∨_W, ∧_W, ¬_W. Identity of profiles proves their Boolean equations, and Plenitude represents them by operations on the admitted type t, with arbitrary defaults outside A if needed.

For any actual family Q^{tt} of atoms, form the individual property

    E_Q(x):=∃a(Atom(a) ∧ Qa ∧ a≤Vx).

By WR, or directly UWR, its profile has a unique representing atom j. Each a in Q has its profile included in j's. If b is any common upper bound, every x in E_Q lies in b's profile, so j≼b. Thus j is the join of Q in the new order. Intersections give meets. No Choice is used; the input family need not be rigid. UWR speaks about its actual extension.

The atoms of (A,≼) are exactly the singleton-profile worlds s_x. Each is nonzero in the new order, because its profile is {x}; any nonzero subprofile is the same singleton. Conversely, any a≠0_W has a nonempty profile (otherwise uniqueness identifies it with 0_W), so some x has s_x≼a. If a is an atom in the new order it must be s_x. Distinct individuals give distinct singleton-profile worlds.

Consequently UWR equips the original world atoms with a complete atomic Boolean algebra whose atoms correspond exactly to individuals. The original propositional Boolean algebra is also complete atomic, with these worlds as its atoms. This gives a fully internal two-stage powerset architecture:

    individuals → world-algebra atoms;
    worlds       → propositional-algebra atoms.

In the full canonical model it is literally D, P(D), P(P(D)). In a general Henkin model the claim is the displayed internal representation and completeness, not the existence of all external subsets.

**Minimal-assumption refinement.** The order-theoretic assertion in this section actually follows from C+UWR_e alone. UWR directly realizes every actual individual profile; no rigidification is needed. Each existing atom a itself represents the current property X_a(x):=a≤Vx, so uniqueness already makes profiles separate. Union, intersection, complement and the arbitrary join E_Q are all current profiles, realized by UWR. The singleton argument is likewise entirely actual. Thus the world support is an internal complete atomic Boolean algebra under ≼ without assuming B, BF, original propositional Boolean Completeness, or Choice. The uniquely defined operations initially have admitted relational graphs; Plenitude is needed only if they are to be represented by operation objects of types tt and ttt. The earlier B-based presentation is a sufficient stronger package, not the minimal premise set.

Conversely, suppose the propositional atoms carry an internal complete atomic Boolean-algebra order ≼, and a relational bijection j identifies its atoms with individuals. Assume Boolean Completeness at the original propositional type and Plenitude at e→t. Define Vx to be the original propositional join of the world atoms a with j(x)≼a. Unique joins plus Plenitude give V. For a current individual property X, take a to be its join in the new world algebra, namely the join of j(x) for Xx. The atom-join lemma, once in each Boolean algebra, gives

    a≤Vx iff j(x)≼a iff Xx.

New-world atomicity makes this representing a unique. Hence UWR_e follows. This supplies an exact structural characterization under the two explicit construction assumptions, and avoids silently importing S5 or full external powersets into the argument.

## 14. Finite tuples of individuals: maximal feasible coordinate types

The WR principle has a natural finite-arity variant with input an n-tuple of individuals:

    WR_{e^n}:=∃V^{e…et}∀X^{e…et}∃w
       (Atom(w)∧∀x₁…x_n(X[x₁,…,x_n]↔w≤V[x₁,…,x_n])).

Here n≥1 is external and finite. These are predicates of n individual arguments, not nonexistent function objects with output e. They should not be silently identified with the one-argument e-instance.

All these principles, even their unique-world versions, are jointly consistent with F and an infinite individual domain in the standard ZFC full S5 models: take D infinite and W=P(D), choose bijections D^n↔D, and use their pullbacks to represent every n-ary relation by a world. For finite D of size m, WR_{e^n} requires and is equivalent over B to at least 2^(m^n) atoms; its unique version is equivalent to exactly that number. Therefore all finite arities give unbounded external finite lower bounds on worlds when m≥2, and rule out a truly finite external world set. This is not a derivation of the impredicative Frege Axiom of Infinity in arbitrary Henkin models. Unique WR at arities one and two already excludes every finite m≥2, though the singleton individual domain remains possible.

Any tuple with even one relational coordinate is impossible for WR, in C alone: fix values in the other coordinates, insert the constant-relation embedding of a proposition in the relational coordinate, and perform Theorem 7's diagonal. Thus finite tuples purely of individuals are exactly the unrestricted coordinate forms for which these full-model consistency constructions can work.

An internal derivation that WR_e implies all WR_{e^n} under individual infinity and F would require an admitted relational pairing/infinite-cardinal-arithmetic theorem. That derivation is not claimed here. An externally infinite full-model cardinal computation is not a substitute for this internal proof, and Frege Infinity alone should not be used as if it were Choice.

## 15. A strict finite-rank hierarchy of world richness

For a coordinate support A^{σt}, define the relativized principle

    WR(A):=∃V^{σt}∀X^{σt}∃w
       (Atom(w)∧∀x(Ax→(Xx↔w≤Vx))).

Define UWR(A) by unique existence of w. Even though X can have arbitrary values outside A, only its extension on A is represented. The empty support gives a trivial WR instance and requires exactly one world under UWR; the hierarchy below starts with inhabited e.

**Supported diagonal.** C alone refutes WR(A) whenever there is a relational injection of world atoms into A. This remains true for multiple disjoint codes. If J(a,x) gives each atom at least one x satisfying Ax, with no x coding two atoms, use

    X(x):=∃a(Atom(a)∧J(a,x)∧¬(a≤Vx)).

WR gives a representing atom w; choose x with J(w,x). Then Ax and uniqueness make Xx↔¬(w≤Vx), whereas representation gives Xx↔w≤Vx. In particular WR on the support of propositional atoms is inconsistent, even though it avoids using all propositions as coordinates.

Now work over B. Set τ₀=e, τ_{n+1}=τ_nt. Define rigid coordinate supports recursively by

    A₀(x):=⊤;
    A_{n+1}(X):=Rigid(X)∧X≤A_n.

Here A_n has type τ_nt, X has that same type, and ≤ is its Boolean-algebra order. A₀ is rigid under □BF; C5's Rigid Power makes every A_n rigid. Thus A_{n+1} is precisely the domain of rigid subproperties of A_n. These are external finite-rank definitions, not object-language quantification over types.

Write WR_n=WR(A_n). The following is a strict ascending hierarchy over F:

    WR_0, WR_1, WR_2, …

To see implication downward, every x∈A_n has the rigid singleton predicate j(x)=λy(A_ny∧y=x), which lies in A_{n+1}; x↦j(x) is injective. Given V at the higher level, put V₀x=V(j(x)). For an arbitrary predicate X on A_n, define Y(z)=∃x(A_nx∧z=j(x)∧Xx). A world representing Y at the higher level represents X at the lower one. No selection is involved.

**Model construction and absence of circularity.** Start externally with any nonempty D. Define sets B₀=D and B_{n+1}=P(B_n), before choosing worlds. Let

    W= ⨿_{n∈ℕ} B_{n+1}.

Take the full S5 model with these worlds and fixed individual domain D. Although the ambient higher-type domains depend on W, the supported rigid domains A_n do not introduce a circular cardinal requirement: by induction, A₀=D, and the rigid predicates supported on A_n are exactly the constant subsets of A_n. Therefore there are canonical bijections A_n≅B_n at every finite rank, regardless of W.

For a fixed n, the map from W to P(A_n) sends a tag-n element to the corresponding subset and every other tagged element to ∅. It is surjective. Its incidence predicate V_n witnesses WR_n by the full-model calibration. Thus all WR_n hold together. In ordinary ZFC the same model satisfies □Functional Choice. The tagged-union construction of the profile surjections itself needs no choices, but the assertion of □Functional Choice is made under ZFC.

**Strictness at each stage.** Instead take W=B_{n+1}. It realizes WR_n exactly, with unique representations. It cannot realize WR_{n+1}: that would give a surjection B_{n+1}→P(B_{n+1}), contrary to Cantor. The same model realizes every lower level. Thus each successor genuinely strengthens its predecessor, even over F. This is not a mere hierarchy of differently named witnesses.

**Why unique representation closes the next stage.** Over B, UWR(A_n) gives an internal bijection from world atoms onto A_{n+1}, by the supported version of §12. But WR(A_{n+1}) is then refuted by the supported diagonal. Thus UWR_n and WR_{n+1} are incompatible. The unique base representation is elegant and exact; the nonunique richness principles instead admit indefinitely higher finite ranks. The notes do not select one of these alternative strengthenings as philosophically compulsory.

This package supplies a mathematically explicit family of consistent strict strengthenings of □Functional Choice, all in the original relational language. It does not establish that □Functional Choice is true in a philosophical sense, or that Maximalism is contradictory. Those conclusions are not licensed merely by a preference for strength and simplicity.

**Schema versus internal infinity (parent audit).** The entire finite-rank WR schema does not itself imply the Frege Axiom of Infinity at t. Indeed, every finite subset of the schema has a full finite S5 model with one individual and sufficiently many but finitely many worlds. That model satisfies all of F and the negation of Axiom-of-Infinity_t. Any hypothetical finitary derivation of a contradiction from F + all WR_n + ¬Axiom-of-Infinity_t would use only finitely many WR_n, contradicting this finite-model observation. Thus the package is syntactically consistent, and under the standard Henkin completeness interpretation has a Henkin model. Such a model is not a standard full model with a truly finite external proposition domain; the impredicative finite-cardinality predicates need not select just externally standard numerals.

For a package intended to assert genuine internal infinity, include Axiom-of-Infinity_e explicitly (and any further desired internal cardinal axiom). The concrete model above with D=ℕ verifies consistency of F + Axiom-of-Infinity_e + all WR_n. The external iterated-powerset or beth_ω description concerns the chosen full model and must not be silently transferred to every Henkin model of the schema.

## 16. Optional probability extension: finite versus countable additivity

This section is ordinary mathematics about the full UWR model, not a claimed principle already formalized in the map. A translation into C would need an explicit representation of the real numbers, of sequences, and of measure operations. The proofs identify what that additional package could consistently require.

Let D be infinite and W=P(D), with its world-group operation symmetric difference. In ZFC there exists a finitely additive probability μ on every subset of W which is invariant under every world translation. To construct it, let I be the directed set of finite subgroups H of the Boolean group W. Every finite subset of W generates a finite subgroup. Choose an ultrafilter U on I containing every tail {H:H⊇H₀}; the tails have the finite intersection property. For each A⊆W put

    μ(A)=lim_U |A∩H|/|H|.

The limit exists in the compact interval [0,1]. Finite additivity, normalization and nonnegativity follow from the corresponding finite averages. For any world g, on the tail where g∈H translation by g permutes H, so μ(A△g)=μ(A), where A△g here denotes translation {a△g:a∈A}, not symmetric difference of event sets. Every finite prescribed binary coordinate pattern has probability 2^{-n}, since coordinate flips permute the 2^n cells of the partition transitively. This gives an explicit consistency construction for fair finitely additive probability on all propositions.

Countable additivity is impossible if every event remains measurable and the measure remains invariant even under the finite-support coordinate flips. Choose countably many distinct individuals. Their finite flips form a countably infinite group H acting freely on W. Choice supplies a transversal T for the H-orbits. The translates hT, h∈H, are pairwise disjoint and cover W. They all have the same measure c by invariance. If c>0, finitely many already have total mass greater than 1. If c=0, countable additivity gives mass 0 to their union W, contradiction. In the full model every hT is a proposition; under the internal world algebra, Boolean Completeness supplies the join of its world atoms and Transversal Choice supplies the analogous orbit selector, once the sequence/group/measure apparatus is fixed.

Thus full event measurability, the strong choice/completeness package, fair translation symmetry and countable additivity cannot all be imposed together. Restricting to a measurable subalgebra, or retaining only finite additivity, avoids this particular obstruction. The argument does not refute the usual product probability measure, whose domain is a suitable sigma algebra rather than every subset of W.

## 17. Raw UWR is compatible with ordinary Pure Maximalism

This section is an important limitation on interpreting the earlier package. The equivalence of UWR with the modal AUCP formulation used B. Without that background, raw world representation need not contradict Pure Maximalism, even with monism at e.

**A Maximalist model with exactly one current atom.** Use the existing proved record `coalesced-pinned-interpretations-root`. Its current propositional domain consists of the finite-pinned, landing intensions on the identity and interpretation arrows. It validates Pure Maximalism, BF and Actuality. Its root singleton a is an atom. It is the only atom: a proposition containing both the identity and another arrow has a as a proper nonzero part. If p contains a nonroot interpretation arrow, take a propositional constant c outside a finite pinning support of p. The proposition ĉ, false at the root and true at an interpretation arrow iff the interpreted c is true, is in the domain: it is pinned by {c}, and its transports land as I(c). Keeping the old support fixed while interpreting c as top or bottom proves that p∧ĉ and p∧¬ĉ are both nonzero. Hence no proposition supported off the root is an atom.

Source caveat: the underlying construction is attributed to Cian Dorr, 19 October 2026, with the domain landing condition and verification supplied by the record's author; its notes say that no second reader has checked the construction. The sole-atom deduction above is new and direct from those stated domains. It is not an independent audit of every part of the entire underlying model.

**Exactly two atoms, one individual, and UWR.** Add one new full coalesced root o above this one component M, using the singleton-individual variant of Appendix E. The sole new individual is sent to any chosen individual of M. At o the propositional Boolean algebra is 2×B_M: a root truth value and an arbitrary component proposition. It therefore has exactly two atoms, a_o (the new root singleton) and the lift of M's sole atom. All the atomless component remainder persists.

The construction is a C-model by the standard coalesced-sum construction. The source family need not itself be complete merely to make a model. Pure Maximalism holds because M already makes every C-consistent pure sentence possible; o sees M, so the same sentences are possible from o by transitivity.

Take V=λx.a_o. For any current individual property X, its extension on the sole current individual is either true or false. Exactly one of the two atoms represents it: a_o in the first case and the lifted M atom in the second. Thus UWR_e holds. The same reasoning gives unique representation for each finite tuple of current individuals, since each such tuple domain is a singleton.

This same V makes the empty-profile agreement proposition ∀x¬Vx equal to ¬a_o, which includes the atomless component remainder and is not an atom. Its agreement with the actual individual's haecceity is a_o. Thus the construction explicitly separates raw unique representation from the old AUCP definition: uniqueness among representing atoms does not say that no atomless possibilities share the agreement condition. Section 32 proves that no alternative V can rescue AUCP in this Maximalist model.

This yields a model of C + Pure Maximalism + individual monism + UWR_e, conditional on the underlying pinned model's stated verification. It does not yield B, Atomicity, or Strong Possibility. Atomicity fails because the nonzero atomless remainder has no atom below it. The fresh root has the standard distinctness-preserving collapse, since its singleton cannot be revisited from its component; the recorded collapse incompatibility therefore refutes Strong Possibility there.

Both current atoms are in fact strong worlds. The new-root singleton transports to bottom along its nonidentity arrow. The lifted pinned-root singleton transports at that arrow to the pinned root singleton, and at every further nonidentity arrow to bottom. At each stage the nonbottom singleton is an atom there and settles every proposition; bottom trivially satisfies the settlement disjunction. Thus Strong Actuality and the assertion that every current weak world is strong also hold. This does not supply Strong Leibniz: the nonzero atomless remainder is still uncovered. Requiring strength of the existing worlds is therefore insufficient to remove the counterexample; requiring their coverage is the crucial additional condition.

More generally, repeatedly adding isolated full roots increases the current atom count by one each time while retaining Pure Maximalism. Thus every prescribed positive finite atom count is compatible with ordinary Maximalism by this construction. Maximalism's possibilities of structures with arbitrarily many atoms do not imply that the current atom count is infinite.

## 18. Atomic ccc and relative countability: no Choice needed

Fix a type σ supplying the Frege number predicate N_σ. Write Ctbl for exactly the relation-based definition Ctbl_{σ,t} from `background.md`, not external countability. Define an antichain family A^{tt} to have only nonzero members and to satisfy p∧q=⊥ whenever Ap, Aq and p≠q.

**Theorem 8.** In C + Atomicity_t,

    Ctbl(Atoms(t))
       iff every antichain family of propositions is Ctbl.

No Choice, Boolean Completeness, BF, or □ND is required. The reverse implication applies the right-hand condition to the atom family, whose distinct members are disjoint.

For the forward implication, let R(a,n) witness countability of atoms. For an antichain A define

    T(p,n):=∃a(Atom(a)∧a≤p∧R(a,n)).

Each p∈A contains an atom, so it receives a number code. If p,q∈A share a number code n∈N_σ, witnesses a,b share that code under R, hence a=b. This nonzero atom lies below p∧q, forcing p=q by the antichain condition. Conversely p=q has a code by the same existence argument. Thus T satisfies the exact displayed definition of Ctbl.

The absence of Choice depends on respecting that definition: a proposition can have many number codes, as long as different propositions have disjoint code sets. No atom is selected uniformly below each antichain member. Replacing this relational notion by the existence of a particular single-valued enumeration would require an additional equivalence argument.

The theorem remains valid when N_σ is finite or otherwise nonstandard in the model. In those circumstances calling it ordinary ccc without the qualifier would misdescribe it; it is the stated relative-countability condition. No external countability or Frege-infinity conclusion is obtained solely from this equivalence.

## 19. A sharp Maximalism incompatibility once atoms cover all possibility

**Theorem 9.** C + Pure Maximalism + Atomicity_t + UWR_e implies the Frege Axiom of Infinity at e, not merely its Infinity Schema. In particular Strong Possibility + Atomicity_t + UWR_e is inconsistent, because Strong Possibility forces individual monism. The finite numeral argument immediately below is introductory; §20 supplies the full impredicative induction establishing the stronger conclusion.

For any fixed external finite m≥1, suppose there are exactly m current individuals. The actual extensions of individual predicates are precisely the 2^m subsets of this finite list; all are available by comprehension. UWR assigns exactly one atom to each extension, and every atom a already represents the extension x↦a≤Vx. Thus there are exactly 2^m current atoms. This part uses C+UWR, not BF or □ND.

In any atomic Boolean algebra with finitely many atoms, every element is the finite join of the atoms below it. If the difference from that join were nonzero, Atomicity would supply a further atom below the difference, contradiction. Hence here there are exactly 2^{2^m} propositions. Pure Maximalism implies the recorded Infinity Schema at t and refutes this fixed finite bound. Since m was arbitrary, every fixed finite individual bound is refuted.

The theorem explains exactly why the two-atom Maximalist model in §17 escapes contradiction: it has a nonzero atomless remainder. UWR gives a complete algebra of worlds, but Atomicity is needed to ensure that those worlds exhaust the original propositional possibilities.

The numeral-by-numeral argument alone gives only the schema conclusion. The upgrade in §20 is necessary to reach the impredicative Axiom of Infinity. The proved-only Engine reports neither a conflict nor a model witness for Maximalism+Atomicity_t itself; that database status is not a claim about the literature.

## 20. Full Frege finite-powerset transfer, in C

This proof uses raw UWR_e exactly as displayed in §12: all current individual predicates X are quantified, without a rigidity restriction. Its equivalence to the older rigid-profile formulation required B, but this proof does not. Write

    Fin_σ(A):=∃Z^{(σt)t}(N_σ(Z)∧ZA).

Thus the negation of Axiom-of-Infinity_σ is Fin_σ(⊤_σ). Every induction below is on the exact impredicative predicate N_σ=FiniteCardinality_σ. No appeal to externally standard numerals is made.

### A. Elementary finite-set closure lemmas

**Coextension invariance.** C proves that each finite cardinality Z is extensional in its property argument: if ∀x(Ax↔Bx), then ZA↔ZB. Prove this by taking as the induction predicate on Z precisely that assertion. It holds for 0 because emptiness is invariant under coextension. If it holds for Z, coextensive A,B have the same possible actual witness a in the definition of Suc(Z), and A−a and B−a are coextensive. Applying the induction hypothesis to these removed predicates proves invariance for Suc(Z). This is invariance of truth of ZA, not an identification of coextensive A and B as objects.

**Adjoining one point.** If Fin_σ(A), then Fin_σ(A∪{a}). Choose N_σZ with ZA. If Aa, coextension invariance transfers ZA to A∪{a}. If ¬Aa, removal of a from A∪{a} is coextensive with A, so Suc(Z)(A∪{a}). The predicates N_σ contain 0 and are closed under Suc by their definition.

**Functional relational images.** If A is finite and R⊆σ×τ is total and single-valued on A, then its image R[A] is Fin_τ. There is no output-type restriction on τ here because R is a relation. Induct on the finite cardinality Z of A, with the induction assertion quantifying over all A and all such R. At 0, A and its image are empty. At Suc(Z), choose a∈A and put B=A−a, with ZB. By induction R[B] is finite. Choose the unique y with R(a,y). Then R[A] is coextensive with R[B]∪{y}; adjoining a point and coextension invariance finish. No global selector is taken.

**Finite unions.** If A and B are finite properties at one type, A∪B is finite. Induct on the cardinality of A, leaving finite B as a parameter in the induction assertion. The empty case is coextensive with B. Removing a successor witness a reduces to (A−a)∪B, followed by adjoining a. Thus finite families of codes may be manipulated without assuming Extensionality, Choice, BF, ND, or Plenitude.

### B. Finite individuals give finitely many worlds under UWR

Fix a UWR witness V and abbreviate the actual bit at x of an atom w by b_w(x):=(w≤Vx). For any individual property A put

    C_A(w):=Atom(w)∧∀x(b_w(x)→Ax).

These are the worlds whose current profiles are supported on A. We prove, by N_e induction on Z,

    ∀A (ZA→Fin_t(C_A)).

At Z=0, A is empty. C_A then consists exactly of the unique world representing the empty individual property, supplied by UWR. A singleton is finite, with cardinality Suc_t(0_t).

For the successor step, let Suc_e(Z)A and choose a with Aa and ZB, where B=A−a. By the induction hypothesis C_B is finite. Define the toggle relation on world atoms by

    T_a(w,v) iff Atom(w)∧Atom(v)∧∀x[
      b_v(x) ↔ ((x=a∧¬b_w(x))∨(x≠a∧b_w(x)))].

For each atom w, raw UWR applied to the displayed individual predicate gives exactly one v. Thus T_a is a total, single-valued relational map on C_B. It is an involution: flipping the same actual bit twice restores the profile, and UWR identifies atoms with the same profile. All these assertions concern actual formulas; no persistence of the toggle is assumed.

There is an actual coextension identity

    C_A = C_B ∪ T_a[C_B].

Indeed a C_A-world with its a-bit false already lies in C_B. If its a-bit is true, toggling a gives a C_B-world and toggling back gives the original. Conversely a C_B-world has a-bit false, and toggling it changes no bit outside A. The relational-image lemma and finite-union lemma make the right side finite. This completes the induction.

For A=⊤_e, C_A is exactly the atom family. Consequently

    C + UWR_e proves Fin_e(⊤_e) → Fin_t(Atoms(t)).

### C. Finite atoms give finitely many propositions under Atomicity

For an atom-subfamily A^{tt}, define

    D_A(p):=∀a(Atom(a)∧a≤p→Aa).

We prove by N_t induction on Z that, for every A consisting only of atoms, ZA implies Fin_t(D_A). At 0, A is empty; Atomicity makes D_A exactly the singleton {⊥}, hence finite.

For the successor step choose a∈A and B=A−a with ZB. Then a is an atom, B is still an atom-subfamily, and D_B is finite by induction. There is an actual coextension identity

    D_A = D_B ∪ {q∨a : D_B(q)}.

To prove coverage, let D_A(p). If a≰p, every atom below p belongs to B, so D_B(p). If a≤p, let q=p∧¬a. Every atom below q belongs to B, and p=q∨a. Conversely D_B(p) implies D_A(p). If p=q∨a with D_B(q), an atom c below p is below q or below a, since atoms are prime for finite Boolean joins. Thus c belongs to B or equals a, and in both cases belongs to A.

The map q↦q∨a is an admitted operation at t, or can simply be used through its functional relation. Its finite image and the union with D_B are finite. This completes the second impredicative induction. Taking A to be all atoms gives D_A=⊤_t, so

    C + Atomicity_t proves Fin_t(Atoms(t)) → Fin_t(⊤_t).

### D. Consequences and scope

Combining B and C gives the exact internal theorem

    C + UWR_e + Atomicity_t proves
       Fin_e(⊤_e) → Fin_t(⊤_t).

Equivalently Axiom-of-Infinity_t implies Axiom-of-Infinity_e under these two premises. Pure Maximalism supplies Axiom-of-Infinity_t by the recorded theorem, yielding Theorem 9's full upgrade. Strong Possibility supplies both Maximalism and monism, and monism supplies Fin_e(⊤_e), so Strong Possibility + UWR_e + Atomicity_t is inconsistent.

The proof imports no Choice, Boolean Completeness, □ND, BF, or unadmitted individual-valued functions. It also does not conflate actual coextension with identity. The crucial repairs compared with a mere finite-numeral argument are (i) induction over all Frege finite cardinalities, including any nonstandard ones admitted by a Henkin model, and (ii) explicit coextension invariance of those cardinalities.

## 21. Relative ccc fails in the infinite world-rich package

The Frege-infinity research agent independently obtains the following stronger consequence in §10 of `.reproduction/classicism-research/frege-infinity-20261022-1726.md`:

    B + Axiom-of-Infinity_e + WR_e
       proves ¬Ctbl_{e,t}(Atoms(t)).

Functional Choice and unique representation are unnecessary. The argument assumes atom-countability, obtains number codes for individuals from worlds realizing singleton profiles, takes least codes in N_e to well-order the individuals, and then uses the internally proved finite-predecessor-segment construction to embed N_e into e under Axiom-of-Infinity_e. Composing atom number codes with this embedding gives a coding of atoms by individuals, contradicting the direct WR diagonal. The precise least-number and Frege-number lemmas are in that agent's cited proof, rather than silently assumed here.

By Theorem 8 and B's Atomicity, the package therefore refutes the corresponding relative ccc. In particular F + Axiom-of-Infinity_e + UWR_e cannot be strengthened by that ccc axiom. This is a sharp limitation on the otherwise strong world-rich package, not evidence that every attractive strengthening of F must be consistent. The conclusion is about the exact e-indexed Frege countability notion; its external ordinary-cardinality interpretation is separately verified in the chosen full models.

## 22. Exact double-powerset representation of propositions

This sharpens the cardinal picture of §§6–9. Work in B and assume UWR_e, with witness V. Let A₁ be the rigid individual profiles and A₂ the rigid subproperties of A₁:

    A₁(X) := Rigid(X),
    A₂(Y) := Rigid(Y) ∧ Y≤A₁.

The types are X:et and Y:(et)t. Rigid Power and the rigidity of the universal individual property give rigidity of A₁. By §§6 and 12 there is an internal bijection f:A₁→Atoms(t). A total representative f of type (et)t can use ⊥ as the default outside A₁; only its restricted graph matters.

For p:t, use Rigid Comprehension to obtain the unique rigid coextension T(p) of

    λX. A₁(X) ∧ f(X)≤p.

Because A₁ is rigid, current inclusion implies T(p)≤A₁, so T(p) belongs to A₂. Uniqueness of rigid coextensions and Plenitude package the assignment as an admitted operation t→(et)t. No arbitrary choice is involved.

Conversely, for Y∈A₂, let U(Y) be the Boolean join of the atoms f(X) for X∈A₁ with YX. Boolean Completeness provides this join, and its uniqueness again permits packaging by Plenitude. The atom–join lemma gives, for every X∈A₁,

    f(X)≤U(Y) iff YX.

Hence T(U(Y)) and Y are coextensive rigid properties, and are identical. For any proposition p, U(T(p)) has exactly the same atoms below it as p. Atomicity gives U(T(p))=p. Consequently

    B + UWR_e proves t ≅ A₂,

in addition to Atoms(t)≅A₁. This is an internal bijection, represented by admitted operations with relational output types.

More strongly, T is an order isomorphism between the original propositional Boolean algebra and A₂ under its inherited order. Indeed Atomicity gives

    p≤q iff ∀a(Atom(a)∧a≤p→a≤q),

and the right side is precisely actual inclusion of T(p) in T(q), which is equivalent to algebraic inclusion because these profiles are rigid. Thus T preserves every admitted join and meet, sends ⊥ to the empty rigid family and ⊤ to A₁, and sends original complementation to relative complementation in A₁. In the full S5 models this is literally

    D,     Atoms(t)=P(D),     t=P(P(D)).

For general Henkin models it concerns the admitted rigid powersets A₁,A₂; it does not identify them with all external subsets.

There is a useful assumption audit here. C+raw UWR alone gives the complete Boolean algebra on *world profiles* in §13. It does not by that argument give completeness of the *original proposition algebra*. In this theorem, Atomicity is used for injectivity of the atom-extension map and Boolean Completeness for its surjectivity; Rigid Comprehension represents the relevant actual extensions by unique entities. Those are separate roles and must not be conflated.

## 23. Countable Boolean independence and weak Dedekind infinity of worlds

Fix a Frege index κ with Axiom-of-Infinity_κ, and write N for N_κ and ν for its relational type. Work in B. The Frege-infinity agent independently confirms that the needed numerical facts follow already from I*_κ: least-number principles for arbitrary admitted predicates, relational primitive recursion, arithmetic and binary digits, and internally finite initial segments. These facts apply also to nonstandard numbers in Henkin models; no external enumeration of N is used.

An operation F:ν→t is **N-independent** if, for every internally finite pair of disjoint subproperties P,Q of N, the finite Boolean meet requiring F(n) for Pn and ¬F(n) for Qn is nonzero. Equivalently, for every m∈N and every admitted pattern on n<m, its corresponding finite Boolean cell is nonzero. The equivalence uses that every internally finite set of numbers has an upper bound, proved by finite-cardinality induction. Boolean Completeness supplies the displayed meets; one could instead include their unique GLB clauses in the definition.

The exact theorem is

    B + Axiom-of-Infinity_κ proves:
    an N-independent family exists
      iff there is an internal surjection Atoms(t)→N.

The right side is weak Dedekind infinity of the atom domain. The statement does not replace surjectivity by an injection N→Atoms without a choice principle.

**Forward.** Given F, for n∈N let

    q_n := (meet of F(m) for m<n) ∧ ¬F(n).

Independence makes q_n nonzero. If m<n, q_n≤F(m) while q_m≤¬F(m), so the q_n are pairwise disjoint. Define the graph J(a,n), on atoms a, by: if a lies below some q_m, assign it that unique m; otherwise assign it 0. The graph is total and single-valued. Every q_n has an atom below it by Atomicity, so J is onto N. Plenitude may package J as an operation, but no arbitrary selection is made.

**Reverse.** Let h:Atoms(t)→N be onto. For n∈N, let F(n) be the Boolean join of atoms a whose h(a) has binary digit n equal to 1. Boolean Completeness and uniqueness of the joins, followed by Plenitude, give the admitted family F. The atom–join lemma says

    a≤F(n) iff digit_n(h(a))=1.

Given internally finite disjoint positive and negative sets P,Q of numeric positions, finite-cardinality induction gives the finite sum k=Σ_{n∈P}2^n. Binary arithmetic gives digit_n(k)=1 for n∈P and 0 for n∈Q. Surjectivity supplies an atom a with h(a)=k. That atom lies below the desired finite cell, which is therefore nonzero. The finite-sum argument is internal induction, not an appeal to an externally finite list or an arbitrary selector.

**Why the index matters.** F+Axiom-of-Infinity_t alone does not make N_e a Peano index: a full model with one individual and infinitely many worlds has Axiom-of-Infinity_t but a truncated N_e. To obtain N_e-indexed countable independence by this theorem, keep Axiom-of-Infinity_e. The unconditional propositional formulation uses κ=t.

**Choice is a real extra resource.** Under F and Axiom-of-Infinity_t, the atom family is not internally finite, by §20.C. The well-ordering consequence of Functional Choice makes it Dedekind infinite; hence it admits an injection N_t→Atoms and therefore a surjection Atoms→N_t (invert on the image and send the complement to 0). The theorem gives an N_t-independent family. This consequence is not attributed to B alone.

As a separate conditional full-model demonstration, suppose the metatheory is ZF with an infinite set W admitting no surjection onto the ordinary natural numbers (an amorphous W would suffice). The full S5 model with worlds W and individuals ℕ satisfies B and both Frege Axioms of Infinity, but its atoms identify with W, so no ℕ-indexed independent family exists. This is conditional on the stated choiceless metatheory; it is not a claim that ZFC contains such a set. It isolates the distinction between infinitude and weak Dedekind infinitude without invoking cardinal comparability.

## 24. Propositional Infinity characterized by self-indexed independence

Under F one has the particularly compact equivalence

    Axiom-of-Infinity_t
      iff there exists an N_t-independent family of propositions.

The forward direction is §23. For the reverse, independence makes the map n↦F(n) injective: distinct n,m are distinguished by the finite pattern requiring F(n) and ¬F(m). The following bare-C lemma, independently proved by the Frege-infinity agent in §17 of its report, then applies:

    an internal injection N_σ→σ implies Axiom-of-Infinity_σ.

The lemma does not assume Peano arithmetic beforehand. If m counts all of σ, finite-cardinality induction supplies a well-order of σ. Associate to each a the unique Frege cardinality of its proper predecessor segment. This is a total injective relational map H:σ→N_σ, and it omits m because the predecessor segment is proper. Composing a supposed injection j:N_σ→σ with H gives an injective nonsurjective self-relation of the finite domain σ, missing j(m), contrary to the C finite-set Dedekind lemma. The supporting exclusivity and proper-subset cardinality facts are proved in the cited report; actual coextension is not silently substituted for identity.

For this reverse direction, the definition of independent family need only cover finite positive/negative patterns, including two distinct indices. It need not assert that N_t is Peano as part of the definition. The theorem therefore supplies the Infinity premise rather than presupposing it in the right-hand side.

## 25. Exact countable compactness boundary

Again work in B+Axiom-of-Infinity_κ, with N=N_κ. Define ωComp_κ as follows: every admitted family F:ν_κ→t whose finite subfamilies have a nonzero common lower bound has a nonzero common lower bound for its entire restriction to N. Boolean Completeness makes this equivalent to saying that the full meet is nonzero. Equivalently, require the initial finite meets to be nonzero, using the internal finite-bounding lemma for numeric indices.

Then

    ωComp_κ
      iff there is no internal surjection Atoms(t)→N
      iff there is no N-independent family of propositions.

The second equivalence is §23. Here is a choice-free proof of the first.

If h:Atoms→N is onto, let r_n be the join of atoms a with h(a)≥n. Every r_n is nonzero, and r_{n+1}≤r_n. Their common lower bounds contain no atom: an atom a with h(a)=k cannot lie below r_{k+1}, by the atom–join lemma. Atomicity therefore makes their full meet zero. This refutes ωComp_κ.

Conversely, suppose F has the finite-intersection property but no nonzero common lower bound. For n∈N put q_n=∧_{i<n}F(i). Each q_n is nonzero. For every atom a there is an index n with a≰F(n), because otherwise a itself would be a nonzero common lower bound. Let h(a) be the least such index. Least-number principles and unique choice give this operation; ordinary Choice is unused. Its image S⊆N is unbounded: for any n, choose an atom a≤q_n; then h(a)≥n.

An unbounded admitted subset S of N has a canonical increasing enumeration f:N→S. Set f(0)=min S and f(n+1)=min{s∈S:s>f(n)}. Unboundedness ensures the recursion is total. It is strictly increasing and f(n)≥n. It is onto: for s∈S, f(s)≥s, so take the least k with f(k)≥s. If k=0 then the minimality of f(0) forces equality. Otherwise f(k−1)<s and the definition of the next S-member gives f(k)≤s. Hence f(k)=s. This proof is internal induction and least-number reasoning, including for nonstandard bounds. The inverse of f on S, composed with h, is the required surjection Atoms→N.

Under F, still retaining Axiom-of-Infinity_κ, this yields

    ωComp_κ iff ¬Axiom-of-Infinity_t.

For the forward implication, if propositions are infinite then atoms are infinite by §20.C; Functional Choice yields a countable atom sequence and hence a surjection onto N. For the converse, finitely many propositions imply finitely many atoms, so no surjection onto the Peano index N exists. Equivalently, in a finite Boolean algebra every finitely satisfiable family has nonzero meet, proved by finite-set induction. The index hypothesis is indispensable: with a truncated finite N_e, an infinite proposition algebra can still satisfy the corresponding finite-index compactness principle.

This is compactness for **all admitted propositional families**, not for a particular chosen set of world coordinates. The distinction matters. Even if a particular V witnesses WR(N), an arbitrary independent family F need not realize all its infinite patterns. Given atoms↠N, the finite-binary-expansion construction in §23 gives an independent F whose all-1 pattern has no atom (each natural number has only finitely many 1 bits). Atomicity makes that full meet zero. Thus universal completion of every independent coordinate system is incompatible with the infinitude package; existential world representation remains feasible.

## 26. Partitions and numerical lotteries: alternative formulations

Under B+Axiom-of-Infinity_κ the conditions in §23 are also equivalent to the existence of an N-indexed partition of ⊤ into nonzero propositions. A surjection h:Atoms→N gives

    p_n := join{a:Atom(a) and h(a)=n}.

These are nonzero and pairwise disjoint. Their join is ⊤ because every atom belongs to exactly one fibre, and Atomicity rules out a remaining nonzero part. Conversely, any such partition assigns each atom to exactly one p_n. The existence assertion follows from the general atom–join lemma: an atom below the join of a family lies below some member, since otherwise every member is below its complement. This direction also uses no Choice.

An equivalent, more modal formulation is the **numerical lottery** principle

    ∃L^{ν_κ t} [□∃!n (N_κ(n)∧L(n))
                 ∧ ∀n(N_κ(n)→◇L(n))].

Over B, numberhood is settled and rigid: positive persistence is the C induction recorded in Goodsell's Lemma 3; C5 gives settled negative instances, and □BF gives the needed inextensibility. Thus the boxed unique-existence clause says precisely that the events L(n), for current numbers n, form a partition of ⊤; the other clause says every cell is nonzero. More explicitly, BF for the rigid number support identifies the Boolean join of those events with ∃n(N_κ(n)∧L(n)), and the necessary unique-existence clause supplies disjointness and exhaustiveness. The converse follows by the same identification. This equivalence should not be exported to arbitrary C models with growing or collapsing number domains.

Consequently, under F, Axiom-of-Infinity_t is equivalent to an N_t-indexed nonzero propositional partition, or equivalently a numerical lottery at index t. For the reverse implication without prior Infinity, pairwise disjoint nonzero cells give an injection N_t→t, and §24's bare-C lemma applies. This gives a short structural reformulation of propositional Infinity in the favored package: a numerical quantity can take each natural value across the space of possibilities while having exactly one value at every possibility.

## 27. Full countable profiles versus finite-pattern independence

Take the supported principles WR(N_κ) and UWR(N_κ) from §15. They quantify over all current properties of the Frege natural-number support. Their input type ν_κ is relational, but the direct contradiction for unrestricted relational coordinates does not apply: only the proper numeric support is used.

Over B+Axiom-of-Infinity_κ, WR(N_κ) implies N_κ-independence, because every finite pattern can be extended to a current numeric property, represented by an atom. The implication is strict. In a full S5 model with D=ℕ and worlds W=ℕ, binary-digit events form an independent family. The numeric support N_κ is externally the standard countable set (take κ=e, or κ=t since W is infinite). But WR(N_κ) would require a surjection from countably many atoms onto all subsets of ℕ, impossible by Cantor. The exact unique version is realized with W=P(ℕ); all full numeric profiles then have one atom each. The individual domain can be chosen independently, including a singleton when κ=t.

All these full models satisfy F in the ZFC metatheory. Thus full countable-profile realization is a consistent substantive strengthening of propositional Infinity and countable finite-pattern independence. It is also compatible with failure of universal ωComp: changing from the witnessing coordinates to the finite-binary-expansion coordinates of §25 produces a different independent family omitting a full pattern. These are distinct quantifier orders, not contradictory verdicts about one axiom.

## 28. Exact finiteness equivalences and a weaker finite-profile principle

The finite-powerset induction of §20 admits a useful symmetric formulation. In C+raw UWR_e,

    Fin_e(⊤_e) iff Fin_t(Atoms(t)).

The forward implication is §20.B. Conversely, singleton profiles supply an injective relational map x↦s_x from individuals to world atoms. If the atom family is finite, its subfamily of singleton-profile atoms is finite by the finite-subset lemma; the inverse singleton-profile relation is a total functional relation on that subfamily whose image is all individuals. The finite-image lemma proves individual finiteness. No individual-valued operation is introduced.

In C+Atomicity_t, independently of UWR,

    Fin_t(Atoms(t)) iff Fin_t(⊤_t).

The nontrivial direction is §20.C; the reverse is closure of finite families under subproperties. Thus C+raw UWR_e+Atomicity_t makes individual, world-atom and propositional finiteness equivalent, and makes the corresponding Frege Infinity assertions equivalent. This is choice-free and concerns impredicative internal finiteness, not merely the external finite-numeral schema.

There is also a weaker useful realization principle:

    FWR_e := ∃V^{et} ∀X^{et} [Fin_e(X)→
                 ∃a(Atom(a)∧∀x(Xx↔a≤Vx))].

It represents every internally finite *total individual profile*. This is distinct from merely satisfying finitely many coordinate constraints: it requires all individuals outside the given finite property to have the false bit. Raw WR implies FWR.

**Choice-free numerical consequence.** C+Axiom-of-Infinity_e+FWR_e gives a total single-valued relational surjection from world atoms onto N_e. For each atom a, form its current profile P_a(x):=(a≤Vx). If P_a is finite, assign its unique Frege cardinality n; otherwise assign 0. Exclusivity makes the first case single-valued. Every n∈N_e is actually instantiated by some individual property X: this is the C equivalence Axiom-of-Infinity_e↔∀n∈N_e∃X(nX), proved in §7.3 of the Frege-infinity report. FWR supplies an atom whose profile is coextensive with X, and coextension invariance of finite cardinalities ensures that atom is assigned n. This proves surjectivity. No atom is selected uniformly for the numbers.

Under B the relational map can be packaged by Plenitude. Sections 23 and 25 therefore give

    B+Axiom-of-Infinity_e+FWR_e
       implies N_e-independent propositions and ¬ωComp_e,

without Functional Choice. Full WR, and a fortiori UWR, have these consequences even if the individual domain itself is Dedekind finite. The numerical map uses the *sizes of finite profiles*, rather than an enumeration of individuals.

FWR is strictly weaker than WR over F+Axiom-of-Infinity_e. In the full S5 model with D=ℕ and W=Fin(ℕ), the incidence predicate V(d)={S∈Fin(ℕ):d∈S} uniquely represents every finite profile. Thus FWR holds. But the world set is countable and the rigid individual profiles form P(ℕ), so WR fails by Cantor. A one-world full model with infinite D refutes FWR, since even the empty and singleton profiles cannot both be represented. These are genuine relative-model separations within the favored background.

This also explains the conditional choiceless picture: with an infinite amorphous individual set D and worlds Fin(D), finite profile sizes already give a surjection of worlds onto ℕ, even though D itself has no such surjection. No claim that such a D exists in ZFC is made; the example is conditional on the explicitly choiceless metatheory.

## 29. Finite generation gives a smaller unique-world axiom

Let **UFWR_e** be FWR_e with a unique representing atom for each internally finite individual profile. It does not require uniqueness, or even realization, for infinite profiles. All statements below use raw current profiles, as in §12.

The Frege Infinity transfer of §20 needs only UFWR_e:

    C + UFWR_e + Atomicity_t proves
       Fin_e(⊤_e)→Fin_t(⊤_t),

and therefore Pure Maximalism+Atomicity_t+UFWR_e implies Axiom-of-Infinity_e. Strong Possibility+Atomicity_t+UFWR_e is inconsistent. To audit the weakening, in §20.B the induction concerns worlds whose profiles are supported on a finite A. Their profiles are finite by the finite-subset lemma, and the one-bit toggles are finite too. Thus UFWR suffices at every use of representation or uniqueness. At the final application A=⊤_e, the hypothesis itself is that this A is finite. The second induction on finite sets of propositional atoms is unchanged.

There is an equivalent local formulation of UFWR. For a fixed V, require:

1. Exactly one world atom has the empty V-profile.
2. For every atom a with finite V-profile and every individual x, there is exactly one atom b whose V-profile differs from a's precisely at x.

UFWR implies both clauses, since toggling one bit preserves finiteness. Conversely prove unique representation of each finite profile X by Frege finite-cardinality induction. The empty case is clause 1. At a successor, choose x∈X and put Y=X−x. By induction Y has a unique representative a. Clause 2 gives a unique toggle b, which represents X. If another atom c represents X, its profile is finite, so toggling x gives an atom representing Y and hence gives a. The toggle relation is involutive: toggling twice restores the original profile, and uniqueness of the second toggle identifies its output with the starting atom. Thus toggling a at x returns both b and c, so b=c. This argument proves the equivalence internally, including for nonstandard Frege-finite supports.

The finite-profile worlds form a canonical Boolean group. Its identity is the empty-profile world, and its addition is profile symmetric difference. Finite-subset and finite-union closure make the result a finite profile; UFWR makes its world unique. Pointwise xor gives associativity, commutativity and a+a=0. These are relationally represented group operations already in C; Plenitude packages them as admitted operations when desired. The group identity is an original propositional atom, not the original false proposition.

Here and in the full world algebra, “canonical” is relative to the chosen witness V. The existential axiom does not select a privileged coordinate system or a unique group operation on the bare atom domain. Different witnesses can transport different algebraic structures onto the same worlds.

The singleton-profile worlds s_x are a basis in the exact internal sense: every finite-profile world is the finite xor of the distinct s_x in its support, and this expression is unique. Existence follows by finite-support induction, and uniqueness follows by examining a coordinate in the symmetric difference of two candidate supports. Thus UFWR canonically realizes the free Boolean group (the direct sum of copies of the two-element group) generated by the individuals. Under full UWR, this group is the finite-support subgroup of the world group of §9, whose full-model form is the product of those two-element groups.

A further optional coverage clause, that every world atom has a finite V-profile, makes all worlds this free Boolean group. In the full models its exact form is W=Fin(D). For infinite D this is distinct from full UWR, whose all-true profile is infinite. The empty-profile and one-bit-toggle formulation is therefore a natural finite-generation alternative to full-profile realization, not a disguised assertion that every arbitrary profile is represented.

## 30. Atomicity as world extensionality

The coverage premise in the Maximalism boundary has a simpler equivalent formulation. In C, Atomicity_t is equivalent to

    WE_t := ∀p q [(∀a(Atom(a)→(a≤p↔a≤q)))→p=q].

Thus propositions are determined by which world atoms they include. If Atomicity holds and p≠q, their Boolean symmetric difference is nonzero and contains an atom, which belongs to precisely one of p,q. Conversely, if p is nonzero but has no atom below it, then p and ⊥ have the same atom extension, violating WE_t. No completeness, rigidity, Choice or modal domain premise is used.

Equivalently, ⊤ is the least upper bound of the atom family. Atomicity makes every upper bound of all atoms equal to ⊤, since any nonzero complement would contain an atom. Conversely, a nonzero atomless p makes ¬p a proper upper bound of all atoms. The formulation does not assume arbitrary Boolean Completeness: it concerns just this one family and identifies its least upper bound explicitly.

Accordingly, the exact incompatible package from §29 may be stated as Strong Possibility + finite unique world-profile realization + world extensionality. Ordinary Pure Maximalism with the latter two principles instead entails actual individual Infinity. The raw two-atom Maximalist countermodel of §17 violates precisely world extensionality: its nonzero atomless remainder and ⊥ are indistinguishable by their atom extensions.

## 31. Strong Possibility: nonunique representation holds, uniqueness fails

The parent research lane has now confirmed a stronger source lemma from its separately audited profile-root construction:

    SP proves Atom_t(A_n), where A_n:=Fregean∧Exactly_n(e),
    for every positive external integer n.

The model and Strong-Possibility transfer proofs are in `.reproduction/classicism-research/profile-root-construction-20261022.md` §§1–6, with a separate audit in `.reproduction/classicism-research/audit-profile-20261022.md`. The parent durable report is `research/2026-10-22/strong-possibility-obstructions.md`. The present corollaries inherit the status of that model lemma; they are not an independent re-verification of its full semantic construction. Only n=1,2,3 are needed here.

The A_n are pairwise disjoint by the C theorem that distinct exact finite individual cardinalities cannot both hold. Each is nonzero because it is an atom. Thus SP gives at least three current propositional atoms, despite forcing current individual monism.

Under monism, raw UFWR_e implies that there are exactly two atoms. Indeed every current individual property is finite and has either the empty extension or the singleton extension. UFWR gives a unique atom for each; conversely each atom a represents its own current profile x↦a≤Vx, so there are no others. The two representative atoms are distinct because their bits differ. Therefore

    SP is incompatible with UFWR_e, hence with raw UWR_e,

**without Atomicity, world extensionality, Choice, BF or ND.** This strengthens the earlier conditional incompatibility in §§19–20 and 29–30. The ordinary Maximalism countermodel with monism and UWR in §17 remains valid: ordinary Max does not itself force the canonical A_n to be atoms.

In the opposite direction, C+monism+two distinct atoms implies raw WR_e. Given distinct atoms a,b, put V=λx.a. A current property true of the sole individual is represented by a; one false of that individual is represented by b, since b≤¬a. Hence

    SP implies raw WR_e while refuting raw UWR_e.

The same contrast holds at every nonempty finite tuple of individual coordinates, since the current tuple domain is again a singleton. Unrestricted relational coordinates remain impossible by the direct C diagonal in §12.

Even the original, rigidity-based UCP_e follows from C+ordinary Max+monism, independently of the profile-atom lemma. To verify this carefully, haecceities H_a(x):=(x=a) are rigid already in C. Persistence is NI. For inextensibility, the hypothesis ∀x(x=a→□Yx) gives □Ya, and necessary identity substitution gives H_a≤Y. Empty profiles are rigid too. Coextensive rigid properties are identical in C: each is necessarily included in the other by persistence of the target and inextensibility of the source. Under monism these therefore exhaust the rigid individual profiles.

Let E₁ say exactly one individual exists and take V=λx.E₁. For any actual individual a, C proves that V agrees with H_a exactly when E₁ holds, and agrees with the empty profile exactly when ¬E₁ holds. The first equivalence uses that E₁ makes every individual equal to a; the reverse follows by evaluating agreement at a. The second uses the nonempty individual domain. Ordinary Max makes E₁ and ¬E₁ possible (the latter has a two-individual full witness). Thus V witnesses UCP_e. In particular SP entails both nonunique formulations.

The raw-UWR argument itself gives no conclusion about the old unique-atomic AUCP_e. Outside B, AUCP and raw UWR need not be equivalent: an atom's truth assignments to current individuals need not settle the extension on individuals that exist only elsewhere. Section 32 supplies a separate, stronger obstruction for AUCP_e.

## 32. Pure Maximalism directly refutes the original unique-atomic principle

This argument is independent of the profile-root construction and its SP atom lemma. It uses ordinary Pure Maximalism with reference theory C, and only finite full S5 models as consistency witnesses.

Fix any candidate V^{et} and any actual individual a. Put

    q₀ := ∀x ¬Vx,
    q_a := ∀x (Vx↔x=a).

As proved in §31, the empty individual property and the haecceity H_a are rigid already in C. Thus AUCP_e makes both q₀ and q_a propositional atoms. They are disjoint: evaluating both agreements at a would require ¬Va and Va.

C proves

    E₁ ≤ q₀∨q_a,

where E₁ says there is exactly one individual. This is a theorem-level entailment, so no optional assumption is illicitly necessitated. At any monist point every individual equals a; if Va is false then V is empty, while if Va is true then V agrees with H_a. Classical excluded middle proves the disjunction. Consequently the algebraic order follows by C's necessity of theoremhood.

Now, for j=1,2,3, let P_j be the closed pure sentence

    E₁ ∧ Exactly_{2^j}(t).

The full S5 model with one individual and j worlds satisfies P_j: its propositional domain is the powerset of its j-element world set, and hence has exactly 2^j members. Thus each P_j is C-consistent, and Pure Maximalism makes all three actual proposition entities P_j nonzero. They are pairwise disjoint by the theorem that distinct exact finite cardinalities cannot both hold. Each lies below E₁, hence below q₀∨q_a.

A join of two atoms cannot contain three pairwise disjoint nonzero elements. For a nonzero p≤q₀∨q_a, Boolean distributivity writes p=(p∧q₀)∨(p∧q_a); each summand is either zero or its atom, so p contains one of those two atoms. Three pairwise disjoint p's cannot share either atom. This is a finite Boolean-algebra argument in C, with no Choice or global Atomicity.

Therefore

    C + Pure Maximalism proves
       ∀V^{et}∀a^e ¬[Atom(∀x ¬Vx) ∧ Atom(∀x(Vx↔x=a))],

and consequently refutes AUCP_e. The universal displayed obstruction is strictly the proof's direct conclusion, rather than merely an existential-axiom failure.

The same proof handles each nonempty finite tuple of individual coordinates: under E₁ its tuple domain is a singleton, so an arbitrary relation is either empty or the tuple haecceity. In fact only the two AUCP instances for the empty profile and one tuple haecceity are required. No current monism premise is needed, and the result is stronger than the SP-specific raw-UWR obstruction.

This reconciles the different notions precisely:

* Ordinary Max+monism entails nonunique UCP_e (§31).
* Ordinary Max refutes unique-atomic AUCP_e by the present argument.
* Ordinary Max+monism+raw UWR_e has the relative model in §17.
* SP entails raw WR_e but refutes raw UWR_e/UFWR_e, using the separately established profile-atom lemma (§31).
* Over B, UCP↔WR and AUCP↔UWR, so the original and improved definitions coincide there.

The direct obstruction may also be read as a finite-cover lemma. Pure Max makes the monism proposition E₁ contain arbitrarily many pairwise disjoint nonzero pure subpropositions, by varying the finite proposition count in its full S5 witnesses. Any principle forcing E₁ below a fixed finite join of atoms contradicts that fact. AUCP supplies the particularly small bound of two.

## 33. Max forces internal Infinity inside each finite-population possibility

The Frege-infinity agent has strengthened the finite-schema fact just used to an internal Frege and Dedekind Infinity theorem. Its detailed proof is §21 of `.reproduction/classicism-research/frege-infinity-20261022-1726.md`; the adaptation below was independently checked in this lane.

Fix a positive standard integer r and let E_r say exactly r individuals exist. Define, for n∈N_t,

    h_r(n):=E_r∧(Suc_t n)(Atom_t),
    Π_r:=∀n∈N_t ◇h_r(n).

Π_r is C-consistent. Take full finite S5 components with r individuals and j worlds, for every j≥1, and add the standard full isolated coalesced root. The full actual-extension coordinate admits a property whose root extension consists exactly of the standard numeral denotations, so the impredicative N_t at the root contains only those denotations (and contains all of them by induction). They are distinct because components with sufficiently many propositions distinguish the corresponding finite cardinalities. For standard n, the component with n+1 worlds has exactly n+1 propositional atoms, making h_r(n) true. Thus the root satisfies Π_r.

Max gives ◇Π_r. Persistence of numberhood and modal 4 pull this back to Π_r, exactly as in the recorded Max⇒Axiom-of-Infinity_t proof. The recorded boxed Exclusivity and Swap lemmas then show that h_r is injective on N_t and that successor is injective there: possible agreement of two h-values supplies a common instance of their finite cardinalities at the atom property, contradicting the boxed incompatibility alternative. The same proof works with Atom_t in place of the source proof's universal individual property; the added E_r conjunction is harmless.

All h_r(n) lie in the Boolean interval

    I_r(p):=(p≤E_r).

Shift h_r(n) to h_r(Suc_t n), and fix every other member of I_r. The resulting admitted relational graph is a total injective nonsurjective self-map of I_r, missing h_r(0). The C Dedekind lemma therefore proves ¬Fin_t(I_r). This is an actual impredicative finite-cardinality conclusion, not just a statement for each standard numeral. The parameter r remains an external fixed positive integer; no internal ∀r statement is claimed.

**Consequences for arbitrary individual profiles.** With q₀,q_a as in §32, Max proves

    ¬Fin_t(λp.p≤q₀) ∨ ¬Fin_t(λp.p≤q_a).

If both intervals were finite, their pairwise-join family would be finite: induct on the first finite family, taking at each successor the finite image of the second under p↦b∨p and adjoining that finite image. This pairwise-join family is exactly ↓(q₀∨q_a), because any p below that join decomposes as (p∧q₀)∨(p∧q_a). Its subfamily ↓E₁ would be finite, contrary to the theorem. Thus Max refutes even the weaker demand that both these agreement propositions have internally finite Boolean intervals, not merely that both be atoms.

Also, the ordinary Max+UFWR_e Infinity transfer can weaken global Atomicity to Atomicity only below E₁:

    ∀p[(p≤E₁∧p≠⊥)→∃a(Atom(a)∧a≤p)].

If all individuals were finite, §29 would make the whole atom family finite. Its subfamily below E₁ would then be finite. The §20.C finite-powerset induction, restricted to propositions below E₁, makes ↓E₁ finite under this local Atomicity premise, again contradicting its proved internal Infinity. This is a dependency refinement, not a claim that the special local premise is philosophically compulsory.

## 34. An explicit ZFC Henkin model separating propositional Infinity from countable independence

This supplies an unconditional ordinary-ZFC semantic example for the Choice gap in §§23–25, replacing the need to rely only on the conditional amorphous-set illustration. This is an independent explicit audit of the finite-support-world permutation model previously mentioned by the parent lane, not a novelty claim; no database/model verdict is edited.

### 34.1 The finite-support hierarchy

Let W be a countably infinite external set, and let G=Sym(W). Individuals are the ordinary naturals, with the trivial G-action. Let D_t be the Boolean algebra of finite and cofinite subsets of W, with its natural permutation action. Recursively, for every admitted function type στ (τ relational), let D_(στ) be ALL finitely supported functions D_σ→D_τ. Here f is supported by a finite S⊆W when πf=f for every permutation π fixing S pointwise; the function action is conjugation, (πf)(x)=π(f(π^{-1}x)). Each entity in the hierarchy has some finite support by construction. Interpret application as ordinary function application, equality crisply as W for equal entities and ∅ for unequal entities, and Boolean operations pointwise.

The modal worlds are the members w∈W, with universal S5 accessibility, the same entity domains at every world, and IDENTITY transport of all entities between worlds. A proposition p is true at w iff w∈p. Crucially, G is a metatheoretic symmetry of this Henkin construction; its action is NOT the modal transport. Confusing these two actions would produce a different model.

Quantification over σ is pointwise intersection or union over the whole D_σ. If f:D_σ→D_t has support S, then ∪_a f(a) and ∩_a f(a) are fixed by every permutation fixing S, hence belong to D_t: a subset of W invariant under Fix(S) is either contained in S or contains all W\S. The quantifier operation itself is equivariant, so it is an admitted entity. The same equivariance argument, by induction on terms, verifies closure under lambda abstraction with finite-support parameters. All actual logical clauses are the ordinary Boolean-valued clauses; contextual βη holds as function equality, and H-equivalent abstracts agree at every world and tuple, hence are identical functions. Thus H and Logical Equivalence hold, and the construction is a C model.

The relational-intension embedding is faithful: different function values differ at some tuple and some world, and the universal identity-transport S5 frame contains that world. No unrepresented function space or quotient equality is assumed.

### 34.2 Why the model satisfies B=C+□Plenitude

There are two direct checks. First, a total single-valued admitted relation U at a world w has a uniquely determined actual selection map f. If U has finite support S, uniqueness shows that every permutation fixing S∪{w} also fixes f. Hence f is finitely supported and, because its output type is relational, belongs to the stipulated operation domain. This proves Plenitude at every world, therefore □Plenitude. It uses only unique determination, not an arbitrary Choice function.

Second, constant domains and identity modal transports give all-type boxed ND and BF. Every nonbottom relation F has some world w and tuple ā where it is true. The relation supported exactly at that tuple and that world is admitted: its support is contained in {w} together with finite supports for the finitely many tuple entries. It is a Boolean atom below F. Thus Atomicity holds at every relational type and every world. This agrees with the recorded equivalence between □Plenitude and C5+Atomicity.

All admitted Boolean joins and rigid coextensions also exist. For an actual admitted family A at world w, its finite support is enlarged only by {w}; its pointwise join is a finitely supported relation. This is Boolean Completeness for admitted families, not closure under arbitrary external subsets. A rigid coextension of an admitted actual relation is obtained by replacing every current true value by W and every current false value by ∅; its support again enlarges only by {w}. Thus the expected B consequences have concrete interpretations.

### 34.3 Both Frege infinities, with standard numerical supports

At every counting type σ, each standard numeral entity is fixed by G because it is the value of a closed pure term. The current subset consisting exactly of the standard numeral entities has an admitted characteristic predicate: give those entities value W and all others ∅. It is equivariant. It contains zero and is successor-closed, so the impredicative definition of N_σ admits no other members. Conversely finite induction gives every standard numeral.

The numeral entities are distinct. Every type has infinitely many current entities: e is ℕ; t has the singleton subsets of W; and constant relations inject t into every relational type. Every finite set of such entities has an admitted characteristic property, using the finite union of their supports. Consequently each standard finite cardinality has a current instance, and distinct standard cardinalities have different extensions. Thus N_σ is exactly standard arithmetic, at every type.

In particular both Axiom of Infinity_e and Axiom of Infinity_t hold. No finite numeral counts the whole infinite current individual or proposition domain. The proposition domain is externally countable, but the next paragraph shows why it is not internally countable.

### 34.4 No atom-surjection onto the naturals

The propositional atoms are exactly the singleton subsets of W. Any admitted current functional relational graph from atoms to N_σ, at world w, defines a finitely supported map, with support contained in the relation's support together with {w}. Every numeral is fixed by every permutation. All atoms outside that finite support lie in one orbit, so equivariance forces them all to receive the same numerical value. The finitely many supported atoms contribute at most finitely many additional values. Therefore every admitted atom→N_σ map has finite image. None is surjective.

Equivalently, for an admitted operation F:N_σ→t, choose one finite support S. Each argument numeral is fixed by Fix(S), so every F(n) is a subset fixed by Fix(S). There are only finitely many such subsets: an arbitrary subset of S, together with the choice whether all of W\S is included. Thus every admitted numerical family of propositions has finite image. It cannot be Boolean-independent.

The same reasoning proves that every internally countable current property of propositions is finite. If an admitted X has its members coded by R into N_σ, take the union of the supports of BOTH X and R, together with the current world. This stabilizer preserves membership in X as well as the coding relation. Any two distinct members in one of its orbits would share a numerical code, contradicting the exact Ctbl condition. Therefore every member is individually fixed by that finite stabilizer, and only finitely many propositions have this property. In particular the whole proposition domain, although externally countable, is NOT internally countable. An external enumeration of the finite/cofinite subsets is not an admitted enumeration.

Consequently this is a ZFC Henkin model of B + AInf_e + AInf_t with no countable independent family, no numerical lottery and no atom-surjection onto N_σ. Every admitted numerical family has finite image, so ωComp_σ holds directly: finite intersection of its finitely many distinct members is nonzero by FIP. This also verifies the exact equivalence from §25 in the model.

### 34.5 Functional Choice fails for an explicit pair selector

Let Two(p) say that p has exactly two propositional atoms below it. Define the admitted, equivariant relation U on propositions by

    U(p,a) iff [Two(p) ∧ Atom(a) ∧ a≤p]
                or [¬Two(p) ∧ a=bottom].

Its truth values are crisp, and it is total at every world. A selecting operation f would have finite support S. Choose distinct u,v∈W\S and put p={u,v}. The transposition of u and v fixes p and every element of S, so it must fix f(p). But U requires f(p) to be either {u} or {v}, and that transposition moves either candidate. Contradiction. Functional Choice fails at the t→t instance, at every world. Since Plenitude holds, an admitted relational selector would also yield such an operation, so the corresponding Relational Choice fails too.

Thus the failure of countable independence is not a hidden failure of Infinity, Atomicity, BC, RC, BF or Plenitude. It isolates a genuine Choice gap inside ordinary ZFC Henkin semantics. The earlier conditional full-model/amorphous example remains correct, but is no longer the only semantic evidence for that distinction.

### 34.6 Internal amorphous worlds, but weakly infinite propositions

The atom property is internally amorphous in this model: it is not Frege-finite, while every admitted current subproperty of it is finite or cofinite relative to the atoms. Indeed, its actual extension is invariant under the stabilizer of its finite support together with the actual world. Outside that support all singleton atoms form one orbit. Membership therefore includes either all or none of them, with only finitely many exceptions. Standardness of N_t makes external finite subsets exactly the internally finite ones in this argument.

By contrast, there is an admitted surjection from propositions to N_σ, for every σ. Send a finite p⊆W to the numeral for |p|, and a cofinite p to the numeral for |W\p|. This function is equivariant and hence admitted. Every natural number occurs, using an n-element subset of W. Thus t is weakly Dedekind-infinite in the surjection-to-naturals sense, although its atom set is not.

There is nevertheless no admitted injection N_σ→t: §34.4 shows that every such admitted numerical family has finite image. For a functional relational graph, Plenitude represents its unique values, giving the same conclusion. This cleanly separates the two directions of numerical coding in a model of B and both Frege Axioms of Infinity.

Finally finite-profile world representation FWR_e fails, because B+AInf_e+FWR_e would provide an atom-surjection onto N_e by §28. The model thus pinpoints the additional world richness that FWR supplies, independently of what Choice supplies.

### 34.7 Stronger: the whole proposition domain is relationally Dedekind-finite

The absence of an admitted N→t injection alone is not used to infer this stronger conclusion. The following direct orbit argument treats even the recorded total left-unique, potentially multivalued Dedekind relation.

Suppose at a world w an admitted relation R on t were total on t, left-unique, and omitted some output q_0. Reverse it: on its output range Y, the relation defines a unique partial function f:Y→t, and totality of R makes f surjective. Enlarge a finite support to include R and w. Then Y is invariant and f is equivariant under the pointwise stabilizer G_S of that finite support S.

Write O=W\S. For each ordinary n≥1, the finite/cofinite proposition domain has exactly c=2^(|S|+1) G_S-orbits isomorphic to the orbit of n-element subsets of O: choose whether the outside part is the n-set or its complement, and choose the inside-S bits. There are also exactly c fixed-point singleton orbits, corresponding to empty or full outside part.

An equivariant map from an n-set orbit to an m-set orbit, with n,m≥1, requires m=n and preserves the outside minority subset. Indeed, the stabilizer of a finite n-set U contains every permutation within U and within the infinite complement O\U. A finite outside minority set fixed by that stabilizer is either ∅ or U. The empty alternative gives a fixed-point orbit; the nonempty alternative gives precisely the same n and U.

To cover all c target n-orbits, a surjective partial equivariant f therefore needs all c source n-orbits, each mapped bijectively to a different target n-orbit. None of these source orbits can be omitted or diverted to a fixed point. This holds for every n≥1. The c remaining fixed points must then cover the c target fixed points, so all are included as well. Hence Y=t, contradicting the omitted output q_0.

Thus the proposition domain is relationally Dedekind-finite in the exact recorded sense, despite Axiom of Infinity_t and despite the explicit surjection t→N. This supplies a direct ZFC Henkin witness to the gap between Frege infinitude, weak numerical infinitude, and the stronger Dedekind condition without Choice.

## 35. Nominal world representation without Choice: an explicit Henkin double powerset

This independently extends the finite-support S5 construction of §34. It is a further model calculation, not a claim that the full-model cardinalities of §4 apply to every Henkin model.

### 35.1 The general nominal S5 recipe

Let A be a countably infinite external set, G=Sym(A), and give the individual domain A its permutation action. Let the modal world set Ω be either Fin(A), or Fin(A)∪Cofin(A). Every world is finitely supported by its finite part or finite complement. Put D_t=P_fs(Ω), the set of all finitely supported subsets of Ω, and at every admitted function type use all finitely supported functions between the previously constructed domains. Accessibility is universal and all modal transports are identities, exactly as in §34.

The quantifier, abstraction, equality, H/Logical Equivalence and relational-intension arguments of §34 apply unchanged. An invariant union/intersection now lies in P_fs(Ω) by definition, without needing it to be finite or cofinite. A unique selector at an actual world u is supported by the relation's support together with a finite support of u. Hence □Plenitude holds. Singleton world propositions are admitted because each world is finitely supported; tuple/world point relations give all-type Atomicity. Thus both models satisfy B, all its recorded consequences, and both Frege Axioms of Infinity. Numerical supports are standard by the same equivariant standard-numeral predicate argument.

Every current individual property has finite or cofinite actual extension in A. Its current extension is fixed by the stabilizer of its own finite support together with a support of the actual world. Outside that finite set, all individuals form one orbit. Conversely every finite or cofinite subset of A has an admitted crisp characteristic property. Thus these are exactly the admitted current individual profiles, at every world.

### 35.2 Full nominal UWR and AUCP

Take Ω=Fin(A)∪Cofin(A), and define the incidence predicate V by

    V(a) := {S∈Ω : a∈S}.

Each V(a) is supported by {a}, and the whole operation V is equivariant, so it is admitted. Its profile at the atom {S} is exactly S. Since every current individual profile is a finite or cofinite S, and Ω contains each such S once, raw UWR_e holds at every world. Over B this is equivalent to the original AUCP_e. Concretely, a rigid individual profile is the crisp characteristic property of some S∈Ω, and its agreement proposition with V is exactly the singleton world proposition {S}.

Functional Choice nevertheless fails. Consider the admitted relation which, for a property P having exactly two current individuals, asks for the haecceity of one of those individuals, and otherwise asks for the bottom property. It is total. If a selecting operation had finite support S, enlarge S by a support of the actual world and choose distinct a,b outside it. The crisp predicate of {a,b} is fixed by their transposition, as is the actual world, while the two permitted outputs H_a and H_b are exchanged. No selector can exist. This is a legal relational-output instance: its input and output types are both et. Consequently this is a ZFC Henkin model of

    B + UWR_e + AUCP_e + AInf_e + AInf_t + ¬FunctionalChoice.

It refutes any inference from unique world representation itself to Choice. It is compatible with adding Choice in other models, as the full S5 models of §4 show.

### 35.3 Internal and external cardinalities must be distinguished

The individual set is internally amorphous, by the same stabilizer argument as §34.6. The world atoms identify with Fin(A)∪Cofin(A). They admit a surjection onto the naturals by the size of the finite side, but admit no numerical injection in the reverse direction: a finite-support family indexed by fixed numerals can take only finitely many world values. More strongly, the exact orbit argument of §34.7 applies to this atom set and excludes even a total left-unique multivalued Dedekind relation on it.

The proposition domain is Dedekind-infinite here. For example, the events 'the finite side of the world has size n' are an admitted equivariant, pairwise disjoint nonzero sequence; shifting their image and fixing the complement gives the required injective nonsurjective graph. This matches §23: countable Boolean independence needs a surjection from atoms to numbers, not an injection of numbers into atoms.

Externally, both A and its world set are countably infinite. The admitted first powerset is only Fin(A)∪Cofin(A), not the full external P(A). The admitted second powerset P_fs(Fin(A)∪Cofin(A)) has external cardinal continuum: already arbitrary unions of the world-size orbits give continuum many invariant propositions, while the full powerset of a countable world set supplies the upper bound. The internal strict world-cardinality distinctions therefore coexist with external countability of both individuals and atoms. The double-powerset representation theorem of §22 is explicitly about admitted rigid profiles, so it applies without claiming external fullness.

### 35.4 A finite-profile version that fails full world representation

Instead take Ω=Fin(A), with the same incidence V. Every internally finite current individual profile is an ordinary finite subset S of A and has exactly the atom {S} representing it. Thus UFWR_e holds, and the original finite-profile atomic agreement version holds as well. Choice still fails by the same two-individual selector.

No alternative admitted V can give full WR_e. Suppose its profile map f:Fin(A)→Fin(A)∪Cofin(A) were onto, as WR would require. Choose a finite support S for V. For any finite nonempty U⊆A\S, equivariance forces a profile with outside part U or (A\S)\U to arise from a source world whose outside part is exactly U: the stabilizer of a finite source set fixes only its outside finite part, its complement, empty, or the whole outside domain. There are only 2^|S| such source worlds, obtained by choosing their inside-S bits. But there are 2^(|S|+1) target profiles with that outside minority set U, obtained by independently choosing finite/cofinite polarity and inside-S bits. Finite pigeonhole makes surjectivity impossible.

Therefore this model satisfies B+UFWR_e+both Inf but refutes WR_e (hence UCP_e over B). It realizes the finite-support Boolean group of §29 while missing the cofinite-profile coset. The richer model of §35.2 adds that coset and realizes the full admitted Boolean profile algebra; neither model has Functional Choice.

## 36. Arbitrarily high finite-rank world richness still does not imply Choice

The nominal construction gives a uniform consistency calibration for the supported hierarchy of §15. All assertions here are ordinary ZFC Henkin-model assertions. No unrestricted WR at a relational input type is introduced; the support guards are essential.

Start with the permuted infinite individual atom set A of §35. Define external nominal sets K_0:=A and K_(n+1):=P_fs(K_n), with their induced permutation actions. Every member of every K_n has finite support. For a fixed n, take Ω:=K_(n+1) as the modal world set and apply the general nominal S5 recipe of §35.1.

The internal rigid profile core at rank n identifies equivariantly with K_n. This is proved by induction and is independent of the choice of Ω. At rank zero it is the individual domain. At the next rank, a rigid property is a crisp characteristic function of a finitely supported subset of the preceding core, zero outside that core. Conversely every such subset has exactly this admitted crisp characteristic function. The core itself is equivariant and crisp. This establishes both directions of the identification, rather than assuming that the ambient higher-type domain is a full external powerset.

Define the supported incidence operation F_n on core elements by

    F_n(x) := {Y∈K_(n+1) : x∈Y},

and set it bottom outside the rank-n core. It is equivariant and admitted. At any actual world, the extension on the core of an admitted current predicate has finite support, enlarged at most by the finite support of that world. It is therefore a member Y of K_(n+1). The unique world atom {Y} represents it. Thus the supported unique WR principle holds at rank n. Repeated union of nominal set families gives surjections K_(n+1)→K_(k+1) for 0≤k≤n, so the corresponding nonunique lower-rank WR principles also hold. The unions have finite support and hence stay in the stipulated nominal powersets.

The two-individual haecceity-selector obstruction from §35.2 is unchanged: at the actual world, enlarge a selector's finite support by the world's finite support and transpose two fresh individuals. Therefore Functional Choice still fails. Both Frege infinities hold as before.

For all finite ranks simultaneously, take instead

    Ω := disjoint union over n∈ω of {n}×K_(n+1).

Each world again has finite support. For rank n use incidence on the tagged n-component and the empty profile on all other components. Every rank-n profile occurs, so WR at that supported rank holds. Hence there is an explicit ZFC Henkin model of

    B + AInf_e + AInf_t + {WR(Core_n):n∈ω} + ¬FunctionalChoice.

The tagged empty-profile worlds even supply an admitted numerical injection into the atom set. Thus the Choice failure is not attributable to a shortage of worlds or to failure of countable independent events; it survives every finite supported world-richness level in this model.

This result complements, rather than weakens, the positive package F=C+□Functional Choice: F proves selection principles that world-profile richness does not supply, while adding the richness axioms to F is independently consistent in the full models already described. The all-rank schema remains a schema; no type quantifier, infinite type, or unannounced infinitary conjunction has been inserted.

## 37. Independent audit of the arithmetic-preserving finite-model bridge

**Purpose and status.** This is an audit of the Frege lane's new conservativity argument, not an independent claim of a theorem from McLarty about Classicism. The source input is Colin McLarty, *Interpreting set theory in higher order arithmetic*, arXiv:1207.6357v5, §§3–5, especially Theorems 5.2–5.3: finite-order arithmetic interprets the required finite-powerset set theories with a definable global well-order. The tree interpretation codes ω by descending sequences of numbers; its constructible/hereditary restriction retains that ω. Source: https://arxiv.org/html/1207.6357v5 . The deductions below spell out the additional Classicism-specific work. Bare mutual interpretability would not suffice for them.

### 37.1 Why the proof requires only finitely many powersets

Fix an actual finite formal proof from C+□Functional Choice+all-type Frege Infinity of an ordinary arithmetic translation A^σ. Enlarge its finite type list to include every subterm type, each auxiliary cardinality type used in the definitions, and all types appearing in the finite H-proofs certifying the Logical Equivalence instances used in the proof. Those H-proofs are part of the proof data required by the original LE theoremhood side condition. This still gives a finite list. No strengthened LE rule relative to the optional assumptions is being used.

In a sufficiently large finite-powerset set theory with choice, construct the corresponding fragment of the full S5 model with

    D_e=ω,    W=ω,    D_t=P(ω),    D_στ=the full function set D_τ^{D_σ}.

Truth at w is membership of w in the proposition; application and lambda abstraction have their usual full interpretations. Products, graphs and every function set on the finite list can be coded within some finite iterate of P(ω). One need not calculate a sharp rank: induction on the finite type list yields a finite bound, enlarged as needed for satisfaction and the cardinality auxiliaries. Replacement forms the required recursion graphs and finite products; the available powersets form the full function sets.

All needed H and LE instances are sound in this full model. For a fixed world w and a total relation U on D_σ×D_τ, set-theoretic choice selects an output for each input; the full D_στ contains the resulting function. Hence every used Functional Choice instance holds at every world, giving its boxed form. This uses the interpreted set theory's choice, not an unproved object-theoretic selection principle.

Every interpreted type is infinite: e contains ω, t contains the singleton-world propositions, and each relation type contains the constant-valued copy of t. The full cardinality-predicate domains make each N_τ precisely the range of the internally defined standard numeral recursion n↦Suc^n(0), for n in that set theory's ω. That range is itself an admitted predicate, contains zero and is successor-closed; induction gives the opposite inclusion. Finite subsets of every size distinguish its numeral values. The corresponding Sum and Prod interpretations are the ordinary addition and multiplication on this same ω, by their recursion clauses and induction. Thus the model validates every Infinity instance occurring in the finite proof, and its translated arithmetic conclusion is exactly the set theory's ordinary arithmetic conclusion.

This is an internal finite-fragment construction. It does not require a set collecting all finite type domains, a completed beth-ω hierarchy, an externally well-founded model of the set theory, or externally standard arithmetic. In a nonstandard set-theoretic model, all occurrences of ω in this paragraph mean its own ω.

### 37.2 The numerical preservation point

The relevant preservation claim is stronger than equiconsistency and weaker than preservation of all higher-order objects. In the tree interpretation, let T_n code the finite ordinal n, and let O be the canonical descending-number tree coding ω. The immediate subtrees of O are exactly the T_n. Consequently

    n ↦ [T_n]

is a definable bijection from the arithmetic input's number sort to the interpreted members of O. It sends zero to the empty-set tree and successor to adjoining the preceding finite-ordinal tree. The arithmetic induction available in the input verifies these statements for every input number, including numbers that are externally nonstandard in a nonstandard input model.

The constructible/hereditary restriction used to obtain the set theory contains O and every T_n; restricting the universe does not add members to O or remove these members. Hence its interpreted natural-number system is this same copy of the input number system. Addition and multiplication are preserved because both sides satisfy their recursion equations, whose uniqueness follows by induction. An induction on first-order arithmetic formulas therefore proves that their truth is preserved. No assertion that the entire tree interpretation is externally well-founded is needed.

Accordingly the source interpretation can be composed with the finite-S5 soundness proof without changing the arithmetic sentence. Separately, the Frege lane's current-extensional quotient construction works with the individual sort replaced by N_σ for any fixed σ under Iσ. It interprets each fixed finite-order arithmetic theory and preserves its number sort, zero, successor, addition and multiplication. Its comprehension verification uses the corresponding finite admissible-type hierarchy in C; it does not assume Choice.

Combining these two arithmetic-preserving interpretations gives the proposed implication

    C+□FC+{Infinity_τ: every admitted τ} ⊢ A^σ
       ⇒ C+Iσ ⊢ A^σ.

The reverse implication follows because Infinity_σ entails Iσ. Thus this audit finds no defect in the bridge, provided its final statement remains about ordinary first-order arithmetic and the original finitary proof systems. It does not prove conservativity for arbitrary higher-order, modal, or world-cardinality assertions. The source theorem and the finite-proof construction, rather than a full external set-model equivalence, are the required proof-theoretic inputs.

## 38. Audit of the finite coalesced-root route to the exact arithmetic shadow of Max

**Status: independent construction audit; the Frege lane owns the complete shadow theorem and its lower inclusion.** Let T denote the ordinary arithmetic shadow of C+Iσ, at any fixed counting type σ. The candidate equality is

    arithmetic consequences of Pure Max = T + all true Π₁ arithmetic sentences.

The upper inclusion requires a stronger argument than merely knowing that Max's axiom set has low arithmetical complexity. This section checks the proposed finite-proof translation. The lower inclusion, including Max's truth of each true Π₁ sentence, must be supplied separately; it is not proved merely by the construction below.

### 38.1 Countable component algebras need no full type hierarchy

Take a fixed finite Max proof. It invokes finitely many maximalist axioms ◇φ₁,…,◇φ_k, with each closed pure φ_i C-consistent. Each arithmetic sentence Con(C+φ_i), for the effective proof presentation including LE certificates, is therefore a true Π₁ sentence. In an internal set theory S with enough finite powersets and global choice, these hypotheses give countable many-sorted Henkin models M_i of C+φ_i.

The component-model construction does not first form full powersets at every type. Present typed H and C as a countable first-order Henkin algebra language: sorts are indexed by type codes; application, the logical operations and abstraction/comprehension instances are effectively listed. LE instances are enumerated with their finite H-proof certificates. Ordinary Henkinization and a Lindenbaum recursion through the formula codes, using the assertion that no internal finite proof yields a contradiction, give a complete consistent Henkin theory. Its term quotient is the required countable typed algebra. All tagged component domains and operations can be coded by sets of natural-number codes. Separation, ω-recursion and Replacement suffice for this countable construction; it does not need one set of all finite powerset levels. Fresh Henkin constants are a conservative language expansion, not a change from pure to signature Maximalism.

This works internally, including when S's ω is externally nonstandard: the consistency hypothesis excludes S's own proof codes, and S's Henkin truth lemma covers its internally coded formulas. Only the externally fixed finite proof and type list will be used in the final transfer.

### 38.2 The root can be built directly as an algebra

Take root individuals D_e=ω^S and choose maps π_i:D_e→D_e(M_i), for example constant maps to chosen component individuals. Surjectivity at e is unnecessary. For each relational type τ=σ₁…σ_l t appearing in the finite proof/type closure put

    D_τ(root)=P(D_σ₁(root)×…×D_σ_l(root)) × ∏_{i=1}^k D_τ(M_i).

At t the first factor is 2. Interpret root truth by that factor. The i-th coordinate is the component projection π_i at relational types. Application takes the corresponding root fiber and applies the component operation to the projected argument. For a lambda term, its first coordinate is its actual root truth extension; its component coordinate is the lambda denotation in M_i with the projected parameters. A logical quantifier's component is the FULL component quantifier, ranging over D_σ(M_i), rather than over the image of π_i.

Induction on terms proves coordinate compatibility. The current first coordinate satisfies ordinary H semantics; every component satisfies H. For LE, the certified H-equivalent bodies have equal current root extensions, and their component abstractions are equal by C in M_i. Thus the root abstractions are identical. This validates exactly the original LE rule. No action-model completion theorem or additional worlds are needed for this algebraic argument.

Because M_i makes φ_i true, its φ_i denotation is not bottom. Therefore the root denotation of φ_i, having this component coordinate, is not bottom, so the root satisfies ◇φ_i. This is the entire reason for adding the components. The root need not satisfy their φ_i actually, and it need not itself satisfy full Pure Max—only the finite collection of Max premises in the given proof.

All the new full root extension factors lie within a sufficiently large finite powerset bound, just as in §37. The component domains were already countable sets in S. Include all proof subterm types and every type in the finite H-certificates used for LE. The resulting domain construction is finite and does not presuppose a completed all-type root hierarchy.

### 38.3 Keeping the arithmetic unchanged

The root individual domain is ω^S. Its arbitrary current extension coordinates admit the range of the internal recursion n↦Suc_e^n(0_e) as a predicate. That predicate is inductive, and Frege induction gives exactly that range as the current N_e. Full current extensions provide finite sets of every internal size, so numeral values are distinct. Current relation coordinates likewise admit the ordinary addition and multiplication graphs; the Sum and Prod definitions consequently give the arithmetic of ω^S. The component coordinates do not affect these current truth calculations.

For a conclusion counted at a general relational σ, add a component M_∞ satisfying C+Infinity_t. The further hypothesis Con(C+Infinity_t) is a true Π₁ sentence, justified externally by the full infinite S5 model; internal Henkin completeness supplies M_∞. Its t-domain is internally infinite in S, since an internally finite domain would have a numeral counting its entire extension. Hence the root t-domain is infinite, and so is every root relational type by the constant-relation embedding. The same current-extension/range argument identifies every required N_σ with ω^S and preserves its Sum and Prod. Using Infinity_t here avoids an unproved substitution of the weaker bare-C arithmetic premise I_t for actual propositional infinity.

Thus S proves, conditionally on finitely many true Π₁ consistency sentences, that the finite Max proof's arithmetic conclusion holds in its own ω. Apply §37's arithmetic-preserving finite-powerset interpretation and then the current-extensional arithmetic interpretation in C+Iσ. This yields the desired upper inclusion in T+true Π₁. It never assumes that an arbitrary external C-consistent sentence is internally recognized as consistent without its explicit true Π₁ premise.

### 38.4 Exact scope of the audit

The construction passes the two potentially serious checks: countable all-type component algebras do not require a full all-type powerset model, and only finitely many full root domains are needed to soundly interpret a fixed finite proof. The numerical preservation is current and internal; no standard-model claim about all Max models is made. A complete theorem statement must still cite the independently proved lower inclusion T+true Π₁⊆arith(Max), retain the effective presentation of C, and distinguish ordinary arithmetic consequences from arbitrary modal or higher-order consequences.
