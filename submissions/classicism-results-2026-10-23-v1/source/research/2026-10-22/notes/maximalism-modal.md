# Modal principles in Maximalist Classicism — original work, 22 October 2026

All claims are in the fixed relational-type C; no optional premise is necessitated. Put

* F := ∀p q ((p↔q)→p=q), the Fregean Axiom.
* PE := ◇F (Possible Extensionality).
* M := ∀p (□◇p→◇□p) (McKinsey).
* G := ∀p (◇□p→□◇p) (.2).
* L := ∀p q [□(□p→q)∨□(□q→p)] (.3).
* Grz := ∀p [□(□(p→□p)→p)→p].

## 1. Possible Extensionality entails McKinsey

C proves F→∀p(p↔□p), and also F→∀p(◇p↔p): the first follows by comparing p with top, and the second by applying the first to ¬p. Thus C proves F→∀p(◇p→□p). Let ◇F and □◇p. At an F-possibility, ◇p holds (by □◇p), hence □p; therefore ◇□p. Universalize p. This proof needs neither BF nor any boxed optional hypothesis.

A purely modal presentation is useful: C proves □(F→(◇p→□p)), hence □◇p∧◇F entails ◇□p by K and its dual.

C also proves F→□F (apply F's truth-to-necessity consequence to F itself). Consequently PE↔◇□F.

## 2. Maximalism entails PE and M, but excludes □M

The ordinary full Henkin singleton model witnesses C+F consistent, so the possibility form of Max(C) gives PE. Section 1 yields M.

The full two-element group model witnesses C+¬M consistent: choose either nonempty proper proposition p. Every world sees p and ¬p, hence □◇p and ¬◇□p. Max(C) therefore yields ◇¬M, contradicting □M.

Thus Max(C) proves M∧◇¬M: a natural universally quantified modal law is true at the evaluation point while failing at some possible point.

## 3. Maximalism excludes even pure .2

C+□F is consistent in a full ordinary Henkin model. C+□¬F is consistent in the full two-element group model, where every world has four propositions and F fails. Max(C) therefore supplies ◇□F and ◇□¬F. The .2 instance at the *closed pure* sentence F turns the first into □◇F. The second contradicts this. Thus Max(C)+.2 is inconsistent; even the schema restricted to closed pure sentences is inconsistent.

## 4. .3 entails .2

Instantiate .3 with p and ¬p. Its first disjunct □(□p→¬p), together with the necessarily valid □p→p, entails □¬□p = ¬◇□p. Its second disjunct □(□¬p→p) analogously entails ¬◇□¬p. Hence ◇□p entails ¬◇□¬p = □◇p. This yields .2. Consequently Max(C) also excludes .3, including its pure-sentence restriction.

## 5. A strengthened consequence of Grz

For any proposition p, write

B(p) := □◇p ∧ □◇¬p, and q(p) := p ∨ ¬◇B(p).

C proves B(p)→□B(p), by 4. We claim C proves

¬q(p) → ◇(q(p)∧◇¬q(p)).                                            (*)

Indeed ¬q(p) gives ◇B(p). At some accessible B(p)-point, both p and ¬p remain possible, and B(p) persists. Move to a B(p)∧p point; q(p) holds there. From there move to a B(p)∧¬p point. At that point ◇B(p) holds by T, so q(p) fails. This is exactly (*), using transitivity (4) for the two successive moves.

The consequent of (*) is ◇(q(p)∧¬□q(p)). Contraposition gives

□(q(p)→□q(p)) → q(p).

This is a theorem of C with p free; theorem necessitation is therefore legitimate and yields

□(□(q(p)→□q(p))→q(p)).

Grz instantiated at q(p) yields q(p). Applying the same argument to ¬p (B(¬p)=B(p)) yields ¬p∨¬◇B(p). Together these imply ¬◇B(p), equivalently □¬B(p).

But ¬B(p) is precisely the McKinsey instance M(p), because ◇□p↔¬□◇¬p. Therefore:

**Grz ⇒ ∀p □M(p)**.

In particular Grz⇒M (T). With BF at type t, ∀p□M(p) gives □∀pM(p), so:

**Grz + BF_t ⇒ □M**.

The intermediate ∀p□M(p) must NOT be confused with □∀pM(p); BF_t is needed for that exchange.

## 6. Maximalism excludes even pure Grz, without BF

Let P be the closed pure sentence saying that there are at least five pairwise distinct propositions. In the recorded full two-object retract model, W0 has four propositions and W1 has eight. Every object reaches both objects: the source category has h:W0→W1 and j:W1→W0, with jh=1_W0. Thus P holds at W1 and fails at W0, and at every world both P and ¬P remain possible. Consequently B(P)=□◇P∧□◇¬P holds in this C-model; it is a closed pure C-consistent sentence.

Max(C) gives ◇B(P). Section 5, applied to the two closed pure sentences q(P) and q(¬P), gives ¬◇B(P) from Grz. Contradiction. BF is not used, because P itself is already a closed term at the evaluation point; no possible quantified witness is pulled back.

## 7. Contrast with C + □Plenitude

The recorded □Plenitude theorem gives □ND, hence 5. Under unboxed 5, PE implies F: F→□F is a C-theorem, so PE gives ◇□F; the dual 5 law yields □F, hence F.

Also M+5 implies F. For any true p, T gives ◇p and 5 gives □◇p. M gives ◇□p, and dual 5 gives □p. Hence every truth is necessary; materially equivalent p,q have necessarily true p↔q, and thus are identical in C. Equivalently instantiate the truth-to-necessity schema at p↔q.

F implies all of PE,M,Grz,.2,.3, since modality collapses to truth; F also implies □F, so their boxed versions follow. Thus over C+□Plenitude, PE, M and Grz are each equivalent to full Extensionality. In contrast Max(C) entails PE and M, refutes Grz, .2, .3 and □M, and refutes F.

## Sources / scope

The arguments in §§1–7 are research derivations by OpenAI Codex (GPT-6), 22 October 2026; §9 separately attributes the already published non-recursive-axiomatizability argument. The finite models and all modal background laws are recorded in the bundle and attributed there:

* Bacon and Dorr, Classicism (16 May 2023 draft), §1.4 pp.15–16 (Fregean/extensionality), §2.4 pp.35–36 (Maximalism), §3.5 p.59 (two-element group and two-object retract), pp.58–61 (action semantics).
* Existing records full-henkin-singleton-base, full-involution-group, full-two-object-retract.

No claim of new-to-the-literature novelty, human checking, or Lean verification is made.

## 8. Improved definitions and a weaker sufficient condition for Strong Possibility

The exact dual form is

D_ne P ↔ ∀q [q→◇(P∧◇q)].

It says that every actual truth remains possible at some P-possibility. Thus pure Strong Possibility can be displayed without introducing an extra modality:

∀q [q→◇(P∧◇q)]  (P closed pure; Max(C)+P consistent).

This preserves the reference theory and makes the return requirement explicit. It does not demand that the P-point itself satisfy Strong Possibility.

A sufficient condition for a Max(C)-model to satisfy pure Strong Possibility is the following metalinguistic property:

For every actual truth p, there is a closed pure truth Q such that Q≤◇p.

Proof: Q is C-consistent. Any model of Max(C)+P satisfies ◇Q, so P∧◇Q is C-consistent. Max at the evaluation point gives ◇(P∧◇Q). From Q≤◇p, theorem 4 gives ◇Q≤◇p, so ◇(P∧◇p), as required. The previously proposed requirement Q≤p is unnecessarily strong. Existence of such a model remains unproved.

A closed pure *Vicinity witness* would suffice: if a closed pure V is true and V≤◇p for every actual truth p, use Q=V above.

### Vicinity as principality of ND-necessity

If v witnesses Vicinity, then for every p,

Box_ne p ↔ ◇v≤p,       D_ne p ↔ ◇(p∧◇v).

Right to left in the first equivalence uses v itself as the witness in Box_ne's definition. Left to right: choose actual q with ◇q≤p. Vicinity gives v≤◇q. Monotonicity and 4 give ◇v≤◇q, hence ◇v≤p. Thus ◇v is the strongest ND-necessary proposition. Conversely, if a true s satisfies ∀p[Box_ne p↔s≤p], then p→Box_ne◇p (witness p) implies s≤◇p for every actual truth p; hence Vicinity. This is an exact alternative definition in C, not an extra axiom.

### Pure-to-signature Strong Possibility

Since Σ contains a relational constant c, signature Strong Possibility implies c≠top_tau: it implies signature Maximalism, and c=top_tau is not a theorem of C(Σ). Any pure Strong Possibility model can be expanded with c=top_tau without changing any pure sentence. Therefore the entailment pure Strong Possibility ⇒ signature Strong Possibility holds only if pure Strong Possibility is inconsistent; conversely inconsistency entails the signature schema by explosion. The database's conjectured arrow is the reverse direction, signature⇒pure, whose consistency side conditions require a separate conservativity argument.

### The pure-term Henkin obstruction

To omit the propositional type {p≠Q : Q a closed pure proposition term}, one must prove it is nonprincipal over a suitable complete extension of Max(C). That requires that every consistent pure formula φ(p) admit some pure closed Q for which φ(Q) stays consistent. Standard Henkin completion supplies new witness constants, not this definable-witness property. The tempting description term ∃p(φ(p)∧p) does not necessarily preserve the witness's intension when uniqueness holds only at the evaluation point. No proof of the needed nonprincipality has been found.

## 9. No effective axiomatization, and no pure-definable Vicinity witness

**Source caveat.** Bacon and Dorr already state and prove non-recursive-axiomatizability of Max(C) in *Classicism*, draft of 1 July 2022, §2.4, p.35 n.52 ([verified primary source](https://andrew-bacon.github.io/papers/Classicism.pdf)). Their enumeration argument immediately extends to the stronger no-consistent-r.e.-extension formulation below. The explicit conservative first-order reduction and the pure-Vicinity consequences are supplied here as added derivations; no new-to-the-literature claim is made. This accessible draft differs from the bundle's cited 16 May 2023 draft.

**Metatheorem.** No consistent recursively axiomatizable theory T extending C can contain every axiom of pure Max(C).

Proof. C has a recursively enumerable proof system: H-proofs and Logical Equivalence instances certified by H-proofs are effectively enumerable. Suppose T is consistent, recursively axiomatizable, and extends Max(C). For an arbitrary closed pure identity A=B, run in parallel the searches for a C-proof of A=B and a T-proof of A≠B. If C proves the identity, the first search succeeds and consistency prevents the second. If C does not prove it, A≠B is a Max(C) axiom, so the second search succeeds. This decides closed pure identity theoremhood in C. By theorem necessitation and T, C proves a closed pure sentence P iff C proves P=top, so pure theoremhood in C would be decidable.

It is not. Given a first-order relational sentence phi(R_1,...,R_n), regard its relation symbols as higher-order variables of the appropriate admitted relational types and form the closed pure sentence forall R_1...R_n phi. First-order validity implies this is an H-theorem, hence a C-theorem. If first-order validity fails, a counterstructure expands to a full ordinary Henkin model of C with its individual domain and full admitted relational domains; interpreting the quantified relation variables by the counterstructure's relations falsifies that sentence. Thus first-order relational validity reduces effectively to pure C-theoremhood, contradicting Church's undecidability theorem. QED. The external theorem used here is Alonzo Church, “A Note on the Entscheidungsproblem,” Journal of Symbolic Logic 1(1) (1936), pp.40–41 ([original paper](https://people.csail.mit.edu/brooks/idocs/church_ent.pdf); see also the [published correction](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/correction-to-a-note-on-the-entscheidungsproblem/2B4D555564730677F94BBBDDC0D7DBC3)). The reduction from that theorem to C is supplied above rather than assumed.

The result applies in particular to a finite extension C+V. It also implies that, if pure Strong Possibility is consistent, no recursively axiomatizable theory over the same effective language can axiomatize or consistently strengthen it, since Strong Possibility entails Max(C). This is a metatheorem about axiomatizability, not an inconsistency proof for either non-effective schema.

**Corollary.** In a Max(C)-model, no true closed pure proposition V can witness Vicinity.

Proof. If V witnesses Vicinity, then for each closed pure C-consistent P, Max gives the actual truth ◇P. Hence V≤◇◇P, and by 4, V≤◇P. The latter is a closed pure identity: at type t, V≤◇P abbreviates (◇P)=(V∨◇P). Max(C) says every closed pure identity not provable in C is false; since this identity is true, C proves it. Thus C+V proves ◇P, for every C-consistent pure P. C+V is consistent because V is true in the given C-model, recursively axiomatizable, and entails Max(C), contradicting the metatheorem.

Consequences:

* No true closed pure proposition can be the Actuality witness, since Actuality witnesses are Vicinity witnesses.
* A Max(C)-model in which every proposition is denoted by a closed pure term must fail Vicinity and Actuality. This rules out constructing such a model among the ordinary full/coalesced-root models with Actuality.
* The pure-cofinal sufficient condition in §8 cannot have a finite basis: if finitely many true pure Q_i suffice, their conjunction is a true pure Vicinity witness.
* The §8 condition can still have an essentially infinite basis, so the obstruction does not refute that possible route to Strong Possibility.

**Infinitary boundary.** These arguments use the effective finitary syntax of C. An arbitrary countable conjunction encoding all Max(C) axioms may itself contain noncomputable information, and a proof system admitting arbitrary infinitely branching proofs need not be recursively enumerable. Merely packaging Max(C) into one infinitary sentence therefore does not contradict the metatheorem. Conversely, adding countable conjunctions to the syntax does not license applying the original Max(C) side condition to the new infinitary identities; that is a change of reference theory and must be stated separately.

### Further exact consequences of the effective-axiomatization obstruction

For every closed pure C-consistent V, there is a closed pure C-consistent P such that C+V+□¬P is consistent. Otherwise C+V would prove ◇P for every C-consistent P and would be a consistent recursively axiomatizable extension entailing Max(C), forbidden above. Accordingly Max(C) gives ◇(V∧□¬P). Thus every consistent finite pure description V can be realized together with a permanent exclusion of some logically possible pure sentence. No finite pure description can certify Max(C).

The same argument works for any consistent recursively axiomatizable extension T of C: there is a C-consistent pure P for which T+□¬P remains consistent. This is stronger than merely saying that T does not contain the displayed Max schema as its literal axioms.

The effectivity issue is exact at the axiom-membership level. C's closed pure identity theorem set is recursively enumerable and at least as hard as first-order validity; the pure Max axiom set is its complement, translated to inequalities. So deciding exactly which inequalities the Max schema commands requires deciding non-theoremhood. This does not make the schema inconsistent: its consistency models remain untouched.

The type {p≠Q : Q closed pure} is locally isolated over Max(C) by p∧Atom(p): this formula is consistent with Max(C), while the corollary excludes p=Q for every pure Q. A model may omit this locally isolated type by omitting Actuality altogether, so this is an obstruction to a blanket omitting-types argument over Max(C), not a proof that pure-generated Max models are impossible.


## 10. Effective presentation and exact ND reflection

**No computable Max algebra.** In every Max(C)-model, two closed pure terms of the same relational type denote the same entity exactly when C proves their identity. Consequently no such model has an effective presentation in which closed pure terms can be evaluated and equality of their values decided: this would decide C's pure identity theoremhood. In contrast, the full ordinary extensional model with singleton individual domain has effectively enumerable finite domains at every admitted type; all its operations and quantifiers are computable, and it satisfies C+□Functional Choice. This is a distinction in effective realizability, not an inconsistency of Max(C).

**C proves (A≠B)→Box_ne(A≠B), with A,B at any admitted common type.** Necessity of identity gives the C-theorem ◇(A≠B)→A≠B. Necessitate this theorem, and use the actual inequality itself as q in the definition of Box_ne. Thus every Max axiom is ND-necessary. Since Box_ne is necessarily normal, every theorem P of Max(C) is ND-necessary under Max(C): a proof uses finitely many Max axioms; necessitate the C-theorem saying their conjunction implies P, and apply normality. No optional premise was necessitated.

Accordingly Strong Possibility gives exact syntactic reflection at this modality. For every closed pure P:

* If Max(C) proves P, Strong Possibility proves Box_ne P.
* If Max(C) does not prove P, Max(C)+¬P is consistent and Strong Possibility proves D_ne¬P, equivalently ¬Box_ne P.

Equivalently, in every Strong Possibility model, D_ne P is true exactly when Max(C)+P is consistent, while Box_ne P is true exactly when Max(C) proves P. The analogous ordinary-diamond fact already holds for Max(C) and C-consistency. This makes the logical role of the stronger schema precise: it repeats exact theoremhood reflection one level up, with a modality that already preserves every Max axiom.

## 11. Strong Possibility has its own modal package

Write B=Box_ne and D=D_ne in this section; all formulas are closed pure. C proves that B is normal S4. Put

E_B := ∀p(p→Bp),
M_B := ∀p(BDp→DBp),
G_B := ∀p(DBp→BDp).

**Strong Possibility entails M_B.** The ordinary coalesced maximalist root validates Max(C)+E_B. Thus Strong Possibility gives D E_B. C proves E_B→(Dp→Bp), since E_B collapses B and D to truth. Under BDp, a possible E_B-point therefore satisfies Bp; hence DBp. Universalize p. This is the same proof as Possible Extensionality⇒McKinsey, applied to the distinctness-preserving modality. Neither BF nor any illicit boxing is used.

**Strong Possibility excludes G_B, even its pure-sentence restriction.** Let E1 say all individuals are identical, and T2=¬E1. The singleton-individual coalesced Max root validates B E1, since it validates E_B. The ordinary coalesced Max root has multiple individuals and validates B T2 for the same reason. Hence Strong Possibility supplies DB E1 and DB T2. G_B at the closed pure sentence E1 turns the first into BD E1, contradicting DB T2. The .3 law for B entails G_B by exactly §4, so it too is excluded.

**Strong Possibility entails D¬M_B.** The recorded coalesced-pinned-substitutions-root is a Max model. Its root endomorphisms are all maps of an infinite set of individual constants; let p=fix_{c} be the proposition saying that the map fixes one chosen constant c. At a root map k, Dp holds: any finite-support truth can be revisited after arranging a map to send k(c) back to c. More precisely the recorded calculation D(fix_S)=delta_S makes Dp true at every root map because every map is injective on {c}. The proposition Dp is false at arrows entering components, where p transports to bottom. Consequently BDp holds at the root: it contains delta_empty, the set of all root maps. But Bp fails at every root map: for any finite S, delta_S contains a bijection sending k(c) somewhere other than c. It also fails in components, where p is bottom. Thus DBp fails, and M_B is false. Therefore Max(C)+¬M_B is consistent, so Strong Possibility gives D¬M_B.

Combining the two results gives M_B∧D¬M_B, hence Strong Possibility excludes BM_B. As in §§5–6, Grz for B implies ∀p BM_B(p); if BF for B at t is also supplied, it implies BM_B and is incompatible with Strong Possibility. Grz for B alone has NOT been excluded by this argument; no exchange of ∀p and B is assumed.

### Optional alternative model for the last consistency claim

A transparent candidate construction is a coalesced maximalist root whose root endomorphism group is the two-element group G. For each original component M_i and g∈G use a separate root-to-component leg, with precomposition by G permuting these legs. Take root individuals to be the product over these legs of the component individual domains, with G acting by coordinate permutation; use the fullest compatible relational domains. The usual coalescence verification should apply unchanged. A root-local proposition u true on both root endomorphisms and empty on component legs makes B quantify precisely over the root G-cluster. A proposition true at only the identity then refutes M_B. Every C-consistent pure sentence remains true in an accessible component, so Max holds. This construction is not needed for the proved result, which uses the recorded pinned model; it is left explicitly as a candidate until the complete fullness/transport verification is supplied.


## 12. Canonical atoms forced by Strong Possibility, and failure at every type

This section depends on the new profile-root construction in `.reproduction/classicism-research/profile-root-construction-20261022.md`, §§1–4, independently audited here. That construction supplies pure Max(C) together with Atom_t(F∧E_n), for every positive standard n. The following arguments are collaborative derivations in the current research session, not database records.

### Universal equality-diagram reflection

If U=∀x̄ θ(x̄) and θ is a finite Boolean combination of typed identities, C proves D_ne U→U. Each identity is □-persistent by NI and hence Box_ne-persistent. Each disequality is Box_ne-persistent by §10. Any true finite conjunction of such literals is therefore Box_ne-persistent. If U fails, choose an actual countertuple and a conjunction of its true literals implying ¬θ; normality yields Box_ne¬U. Contrapose. No BF is needed.

Atom_τ(a), for fixed a, belongs to this universal equality-diagram fragment: algebraic order is an identity of Boolean terms, and nonbottomness is a disequality. Consequently Strong Possibility forces Atom_t(A), where A=F∧E_1, since that sentence is consistent with pure Max in the profile-root construction.

### Pure SP excludes signature Max in every expansion

Let c be any relational constant of Σ, of type τ, and put P(c):=(c=top_τ). The two closed Σ sentences A∧P(c) and A∧¬P(c) are each C(Σ)-consistent: use the full extensional singleton-individual model, interpreting c as top or bottom respectively. Signature Max makes both nonbottom. They are disjoint parts of A, contradicting Atom_t(A). Thus pure Strong Possibility is incompatible with signature Maximalism for EVERY permitted signature containing a relational constant. This needs neither Infinity nor an individual constant, and is stronger than the elementary non-entailment argument from interpreting a fresh constant as top.

### Atomicity persists under Box_ne if the corresponding Barcan instance holds

For a relational type τ, C proves

BF_τ ∧ Atom_τ(a) → Box_ne Atom_τ(a).

Use the Boolean-algebra equivalence

Atom_τ(a) ↔ a≠bottom_τ ∧ ∀p^τ(a≤p ∨ a≤¬p).

Each disjunct a≤p or a≤¬p is an identity. NI therefore turns their actual disjunction into its ordinary box. Universalize p and apply BF_τ to obtain □∀p(a≤p∨a≤¬p). Ordinary necessity implies Box_ne necessity. Also a≠bottom_τ is Box_ne-persistent by §10. Normality combines the two clauses into Box_ne Atom_τ(a). This proof never assumes that disequality is ordinarily necessary.

The reduct of a signature-Max model witnesses pure Max+¬Atom_t(A) consistent, by the splitting argument. Hence Strong Possibility gives D_ne¬Atom_t(A), while it already forces Atom_t(A). The displayed persistence lemma therefore proves

**Strong Possibility ⇒ ¬BF_t.**

### Retracts propagate the obstruction to every relational type

For every relational σ=τ_1…τ_k t, C proves BF_σ→BF_t. Choose an actual tuple ā of the argument types (nonempty domains are part of H), and define c(p)=λx̄.p and r_a(F)=Fā. The beta identity r_a(c(p))=p is a C-theorem, with ā free; all necessitations of it are legitimate. From ∀p□Pp infer ∀F□P(r_aF). BF_σ gives □∀F P(r_aF). At every possible point instantiate F=c(p), giving □∀pPp. No surjectivity of transport is assumed; the retraction is supplied by lambda terms themselves.

Thus Strong Possibility refutes BF_σ at every relational type. The independently proved monism argument refutes BF_e. Together:

**Strong Possibility forces failure of the Barcan formula at EVERY admitted type.**

For every input type σ and relational output type τ, Functionality_(σ,τ) implies BF_σ. Given ∀x□Px, compare F(x)=c_τ(Px) with the constant top_τ operation. Their values are actually identical at every x; Functionality identifies the operations. NI preserves that identity, and the left inverse r_a of c_τ recovers Px=top at every possible x, yielding □∀xPx. Therefore Strong Possibility refutes EVERY admitted type instance of Functionality, not merely the all-types schema.

### Independent higher-type atom generalization

For relational σ=τ_1…τ_k t define the closed pure term

a_σ := λx_1…x_k . A ∧ ∧_{i:τ_i≠e}(x_i=top_{τ_i}).

When k=0, a_σ=A. At an F∧E_1 point each e argument is the unique individual, and every other argument is forced to be its type's top. Thus this term selects a single tuple. In the profile-root construction, any root relation has a profile given by a pure term T(z), with one individual parameter. At the unique finite extensional structure satisfying A, the truth of T at the selected tuple is independent of the component and of z. Consequently its meet with a_σ has profile either bottom or a_σ. Both have empty actual extension because A is false at the root. The nonzero a_σ is therefore a Boolean atom. This works simultaneously at every relational type.

Hence pure Max+Atom_σ(a_σ) is consistent, and universal equality-diagram reflection gives

**Strong Possibility ⇒ Atom_σ(a_σ), for every relational σ.**

Signature Max splits these canonical atoms by the two scalar predicates c=top and c≠top just as above. This supplies an independent route to every relational BF failure through the atom-persistence lemma, although the retract argument is shorter.


## 13. Atomless ND-possibilities and downward transfer of lattice principles

### Canonical atoms can become wholly atomless

Let a_σ be §12's canonical atom at any relational type. The recorded coalesced-pinned-interpretations-root validates

AtomlessBelow_σ(a_σ) := ∀p^σ[(p≠bottom ∧ p≤a_σ)→¬Atom_σ(p)].

Proof. Its auxiliary signature has infinitely many propositional constants. Let nonzero p≤a_σ have finite pinning set S. Since a_σ has empty actual extension, nonzero p is witnessed at some interpretation arrow ⟨V,I⟩ and some argument tuple. At that point A=F∧E_1 holds. Choose a propositional constant c outside S. Vary I(c) between top and bottom, leaving every other interpretation fixed. Pinning preserves p at the same tuple, and the pure a_σ is unaffected. The two relations p∧const_σ(c=top) and p∧const_σ(c≠top) are disjoint nonzero parts of p, so p is not an atom. This works for every such p. The model satisfies pure Max.

Therefore Strong Possibility entails D_ne AtomlessBelow_σ(a_σ). Since a_σ≠bottom is ND-persistent, it entails the stronger conjunction

D_ne(a_σ≠bottom ∧ AtomlessBelow_σ(a_σ)).

Thus at every relational type SP forces an actual canonical atom that can become a nonzero element with no atoms below it under the distinctness-preserving modality. Every actual entity already decides that atom by a positive-identity disjunction; those decisions persist. The splitting entities therefore cannot all be transported old entities. This supplies concrete witnesses to the all-type Barcan failures.

### Every single relational Atomicity or Strong Leibniz instance descends to t

For every relational σ, C proves Atomicity_σ→Atomicity_t and StrongLeibniz_σ→StrongLeibniz_t. These are stronger type-wise statements than specializing an all-types schema to t.

Let c_σ(p)=λx̄.p and π_σ(W)=∃x̄ W x̄. C proves π_σ(c_σ(p))=p, that π_σ preserves bottom and order, and that W≠bottom implies π_σ(W)≠bottom. The last fact follows because a relation is bottom exactly when its existential projection is bottom.

Given nonzero p, apply Atomicity_σ to c_σ(p), obtaining an atom W≤c_σ(p). For every proposition q, W decides c_σ(q). Applying π_σ shows that π_σ(W) decides q; it is a nonzero atom below p. This gives Atomicity_t.

For Strong Leibniz, take a strong W instead. Its necessary universal decision property applies, at every possible point, to every constant relation c_σ(q). Projection therefore gives □∀q[π_σ(W)≤q∨π_σ(W)≤¬q]. Thus π_σ(W) is a strong t-world below p. No Barcan exchange is used: the constant relation is formed at the possible point where q is quantified.

Since Strong Possibility excludes Strong Leibniz at t, it excludes EVERY single relational Strong Leibniz instance.

### Boolean Completeness descends similarly

For each relational σ, C proves BooleanCompleteness_σ→BooleanCompleteness_t. Given a property X of propositions, form the property of relations consisting of c_σ(p) for Xp. Let G be its greatest lower bound. Put u=∀x̄ G x̄. The C-theorem

c_σ(q)≤G ↔ q≤∀x̄ G x̄

follows by moving q, which has no free x̄, through the universally closed implication. Since c_σ reflects order, q is a lower bound of X exactly when c_σ(q) is a lower bound of its constant image, exactly when c_σ(q)≤G, exactly when q≤u. Hence u is the required greatest lower bound. No BF is used.


## 14. Pure strong-world exclusion and the exact pure-atom criterion

### Maximalism forbids every closed pure strong world

Fix a closed pure relational term W. If C proves W=bottom, it cannot be a strong world. Otherwise C+(W≠bottom) is consistent. Take a component model witnessing this and coalesce TWO disjoint copies of it at a new fullest root, using the ordinary finite coalescence construction. A root scalar proposition p with top profile in one component and bottom profile in the other splits the pure W: both W∧const(p) and W∧const(¬p) are nonzero. Thus C+(W≠bottom∧¬Atom(W)) is consistent.

Pure Max consequently gives ◇(W≠bottom∧¬Atom(W)). But C proves

SWorld(W)→□(W≠bottom→Atom(W)),

because a strong world's necessary decision property, together with its remaining nonzero, is precisely atomicity. Contradiction. Therefore, for EVERY closed pure relational W,

**Max(C) entails ¬SWorld(W).**

This is a schema about pure terms, not the internal sentence saying that no strong worlds exist. Strong worlds, if present, must be unnamed by closed pure terms.

Since BF_σ turns every actual weak σ-world into a strong σ-world, Max+BF_σ forbids every closed pure σ-atom. Consequently the SP⇒¬BF_t proof can be shortened: SP forces the canonical pure atom A, BF_t makes it a strong world, and Max already excludes every pure strong world. No separate Max+¬Atom consistency side condition is needed in this shorter route.

### Exact classification of Max-consistently atomic pure propositions

For a closed pure proposition A, define the following EXTERNAL condition PC(A):

1. C+A is consistent.
2. For every pure proposition term P(x) with at most one free individual variable x, either C proves ∀x(A→P(x)) or C proves ∀x(A→¬P(x)).

Then:

**Max(C)+Atom_t(A) is consistent iff PC(A).**

Necessity. If PC's first clause fails, A=bottom is a C-theorem. If its second clause fails for P(x), both pure one-variable formulas A∧P(x) and A∧¬P(x) are C-consistent. Unary Possibility+, which pure Max entails, gives their possibility for every actual individual a. Hence A is split by P(a), contradicting Atom(A).

Sufficiency. Use the profile-root construction, whose every root proposition has a pure one-individual-variable profile T(z). PC(A) ensures that A∧T(z) has profile either A or bottom. We must also show that A's actual root coordinate is false. PC(A) implies C+A is complete for closed pure sentences, by taking P independent of x. If A were true in any Max model, consistency of the complete r.e. theory C+A with that model would force it to prove every Max axiom: it decides each such axiom, and cannot decide it negatively. This contradicts the no-consistent-r.e.-extension theorem. Thus A is false at the profile root. Arbitrary actual coordinates therefore cannot split A; its meet with any root proposition is either A or bottom. Since C+A is consistent, its profile is nonzero. Thus Atom(A) holds in that Max model.

This is pointed completeness, not merely completeness for closed pure sentences. The additional one-individual-variable condition is essential to the proof and is exactly what the profile model and unary Possibility+ detect.

Universal equality-diagram reflection now yields an exact description under Strong Possibility:

**SP entails Atom_t(A) exactly for the closed pure A satisfying PC(A); otherwise Max already entails ¬Atom_t(A).**

This describes the pure atomicity diagram without assuming consistency of SP. If SP is consistent, every SP model has exactly these pure atoms.

### Pure atoms cannot enter the canonical arithmetic region

A simpler necessary consequence is useful independently. In a Max model, any closed pure atom W makes C+W a consistent complete pure theory: W decides every pure P, and the resulting true closed identity W≤P or W≤¬P must be a C-theorem by Max's reflection of pure identities.

Let I_σ be the topic's arithmetic antecedent. If W∧I_σ were nonzero, atomness would force W≤I_σ, hence C would prove W→I_σ. Then C+W would be a consistent recursively axiomatizable complete extension of the canonical Peano arithmetic interpretation supplied by Goodsell's Lemma 1, contradicting the incompleteness theorem for consistent r.e. extensions of arithmetic. Therefore every closed pure atom under Max satisfies W≤¬I_σ. This uses exactly the arithmetic interpretation prerequisite already cited in `possibility-and-necessity-of-arithmetic-incompatible`; it is not inferred merely from first-order syntax being present. The finite extensional atoms F∧E_n fall outside I_σ, as expected.

## 15. Rigidity audit: the nullary case is automatic

Original argument, Codex, 22 October 2026. No record edits. The record `tame-rigidity-and-rigid-power-imply-weakly-rigid-power` is conjectured; only the version with necessary Tame Rigidity is proved. Its final note incorrectly says a countermodel must fail necessary Tame Rigidity at type t. In fact C proves that entire nullary instance, and also the nullary instances of both power principles.

For a proposition p,

    WeaklyRigid(p) iff (p=top or p=bottom) iff Rigid(p).

If p is true, weak persistence gives □p. If p is false, weak inextensibility, tested on bottom, gives p≤bottom, hence □¬p. Conversely, a necessary or impossible proposition is weakly rigid directly. The disjunction □p∨□¬p is persistent by 4, so weak rigidity is necessary and p is rigid. The proof is a C theorem with p arbitrary; its universal closure and necessitation are C theorems, without BF.

At proposition type, the weak or rigid power property of bottom is λq(q=bottom), and that of top is λq(q=bottom∨q=top). Each is a finite union of haecceities. Haecceities at every admitted type are rigid in C: NI supplies persistence, and any necessary property of a is necessarily true of anything identical to a, which gives inextensibility. Finite unions of rigid relations are rigid (test each summand against a proposed necessary cover). Thus Rigid Power_t and Weakly Rigid Power_t are C theorems. Here “_t” means the input relation F is a proposition; the resulting power property has type tt.

More generally, suppose a relation F has the externally finite actual extension {a_1,...,a_n}, where a_i are tuples, and F is weakly rigid. Let G be the finite union of the corresponding tuple haecceities. G is rigid. Weak persistence of F and actual membership of each a_i give G≤F. Weak inextensibility of F applied to G gives F≤G, because each actual F-tuple necessarily satisfies its own haecceity. Hence F=G, so F is rigid.

For every subset I⊆{1,...,n}, let G_I be the finite union of the haecceities of a_i for i∈I. Let Q be the finite union of the haecceities of the relation entities G_I. Q is rigid. Necessarily every G_I is weakly rigid and below F. Conversely, at any accessible world, any weakly rigid H below F has extension contained in the finite set of transported a_i. The preceding finite-extension argument at that world identifies H with some transported G_I. Thus Q is necessarily coextensive with the weak power property of F, and they are identical. This proves Weakly Rigid Power locally at F, and likewise Rigid Power.

Consequences: every counterexample to Tame Rigidity has a weakly rigid relation with externally infinite actual extension; every counterexample to Rigid Power has a rigid relation with externally infinite actual extension; every counterexample to Weakly Rigid Power has a weakly rigid relation with externally infinite actual extension. This is an external finite-list theorem, uniformly for each finite n. It must not silently be conflated with an internally finite, possibly nonstandard extension.

An additional internal result is secure: every internally finite unary property has a rigid coextension in C. Use induction in the topic's impredicative definition of finite cardinality. The empty property has bottom as rigid coextension. For a successor-counted property X, choose its distinguished element a, apply the induction hypothesis to X minus a, and adjoin the rigid haecceity of a; finite union preserves rigidity. Therefore every internally finite weakly rigid unary property is rigid: compare it with that rigid coextension, applying weak inextensibility in both directions and persistence. Extending the internal proof to finite power properties requires a separate induction; the externally finite result above does not by itself supply that extension.

## 16. Atomicity and Rigid Comprehension imply Weakly Rigid Power

Original adaptation, Codex, 22 October 2026, of the proved database write-up `atomicity-and-rigid-comprehension-imply-rigid-power.md`, whose source is Bacon, *Could the truths of mathematics have been different?*, Appendix C.2, Lemma C.6, pp. 15–16, together with the coextensive-weak-rigidity lemma attributed there to Christopher Sun. The adapted theorem is not claimed to occur in those sources. No record or Lean changes.

Fix τ=σ̄t. It is sufficient to assume Rigid Comprehension at τ and Atomicity at τt. No BF, necessary comprehension, or Rigid Comprehension at the power-property type is used. We prove the τ instance of Weakly Rigid Power.

Let F^τ be weakly rigid and put P(Y):=WeaklyRigid(Y)∧Y≤F. Rigid Comprehension at τ implies Tame Rigidity at τ: if Y is weakly rigid, choose a rigid Z coextensive with Y; coextensive weakly rigid relations are identical, so Y is rigid. Consequently P is weakly persistent at the evaluation point: P(Y) implies that Y is rigid, hence necessarily weakly rigid, and Y≤F is necessary by NI/4. Thus P(Y)→□P(Y). This is only weak persistence; no universal quantifier has been moved through a box.

We first prove the atom pullback claim: if W^(τt) is an atom and W≤P, there is an actual weakly rigid X≤F such that

    □∀Y (W(Y)→Y=X).

Use Rigid Comprehension at τ to choose rigid X coextensive with

    Q(x̄):=F(x̄)∧□∀Y(W(Y)→Y(x̄)).

(a) X≤F. Every actual X-tuple belongs to F and therefore necessarily belongs to F, since weak rigidity implies persistence. Weak inextensibility of X applied to F yields X≤F. Thus P(X).

(b) □∀Y(W(Y)→∀x̄(X(x̄)→Y(x̄))). If X(x̄) holds actually, Q's definition gives □∀Y(W(Y)→Y(x̄)). Weak inextensibility of X applied to λx̄.∀Y(W(Y)→Y(x̄)) gives the displayed boxed implication after permuting quantifiers inside that same box.

(c) □∀Y(W(Y)→∀x̄(Y(x̄)→X(x̄))). Fix an actual F-tuple x̄. If X(x̄), rigidity of X gives □X(x̄). If ¬X(x̄), its actual coextensivity with Q and F(x̄) give ¬□∀Y(W(Y)→Y(x̄)), namely W not≤ λY.Y(x̄). Atomness of W therefore gives W≤λY.¬Y(x̄). Either case gives □∀Y(W(Y)→(Y(x̄)→X(x̄))). Apply weak inextensibility of F to λx̄.∀Y(W(Y)→(Y(x̄)→X(x̄))). We obtain □∀x̄(F(x̄)→∀Y(W(Y)→(Y(x̄)→X(x̄)))). Since W≤P, necessarily W(Y) implies Y≤F, and hence actual containment in F at that reached world. The desired implication follows inside the box.

(d) Work at an arbitrary accessible world with an arbitrary Y there satisfying W(Y). The hypothesis W≤P supplies WeaklyRigid(Y) at this very world; it is not being inferred from an old-world universal or from an unboxed premise. Rigidity of the chosen X persists, so X is weakly rigid there. By (b) and (c), X and Y are coextensive there. The C theorem that coextensive weakly rigid relations are identical gives Y=X there. Universal closure at each reached world proves the atom pullback claim. This is the exact point at which the original proof's stronger Rigid(Y) assumption can be replaced by WeaklyRigid(Y).

Now prove P weakly inextensible. Let Z^(τt) satisfy ∀Y(P(Y)→□Z(Y)). Suppose P not≤ Z. Then P∧¬Z is nonbottom. Atomicity at τt gives an atom W≤P∧¬Z. The claim gives an actual X with P(X) and □∀Y(W(Y)→Y=X). The cover hypothesis gives □Z(X). But W is nonbottom, so it is possibly instantiated; at such a world choose Y with W(Y). There Y=X and ¬Z(Y), contradicting □Z(X). Thus P≤Z. Together with weak persistence, this is WeaklyRigid(P), exactly Weakly Rigid Power at F.

The theorem is a C derivation from the stated local premises, so its correctly boxed companion follows by necessitating the C implication and using normality: □Atomicity+□Rigid Comprehension imply □Weakly Rigid Power. The theorem does not turn unboxed Atomicity or comprehension into their necessities.

Clarification to §14's phrase “SP entails Atom(A) exactly when PC(A)”: this is a semantic classification conditional on SP consistency, not an unconditional syntactic biconditional. The proved statements are PC(A)⇒SP⊢Atom(A) and ¬PC(A)⇒Max⊢¬Atom(A). An inconsistent SP would of course prove both. The corresponding profile-construction note §12 states this caveat explicitly.

### Independent audit of the fixed-point cone

The construction in `rigidity-actualization.md` §25 has root relational Boolean algebras P(A-tuples)×P(B-tuples/G), so besides Atomicity and Rigid Comprehension it has Boolean Completeness and Relational Choice at every type, and Strong Actuality (the root-only proposition is a true strong world). It refutes ND: two pairs with equal tail profile but different actual extension become identical at the tail. The §16 theorem gives WRP. The inherited tail weak nonrigid relation yields failure of □Tame Rigidity.

Every BF instance fails there. At e, the root singleton becomes an infinite tail. At t, write r for the root-only proposition. The four root propositions all transport to top or bottom, so every current p necessarily satisfies Q(p):=r∨p=top∨p=bottom. At the tail r is false and a contingent proposition violates Q. Thus BF_t fails; BF_σ⇒BF_t for each relational σ yields failure at every other relational type. There are also no Strong Leibniz Biconditionals at any relational type. The tail-only root proposition ¬r is itself a root atom, so it is the only nonzero proposition below itself; its tail image is top, which is not a tail atom, so ¬r is not a strong world. This refutes SL_t, and the individual-instance transfer SL_σ⇒SL_t refutes each relational SL instance. These are direct verified verdicts, not merely schema failures.

## 17. Images, unions, and lowering the rigidity type

Original elementary deductions in C, Codex, 22 October 2026; literature novelty unchecked. These are per-instance transfer theorems, stronger than merely specializing an all-type schema. No additional modal or choice axioms are used.

### Two closure lemmas

**Direct images.** If F^σt is weakly rigid and f:σ→τ is an admitted operation (τ≠e), its relational image I(y):=∃x(Fx∧f(x)=y) is weakly rigid. Weak persistence follows from persistence of F and NI. If every actual I-instance necessarily satisfies Z, then every actual F-instance x necessarily satisfies Z(f(x)). Weak inextensibility of F gives □∀x(Fx→Z(f(x))), hence I≤Z. The argument is a C implication, and so when F is rigid it applies at every reached world to give rigid I. Finite tuples in place of σ are handled by the same existential formula, with an operation of the admitted relational output type.

**Unions.** Let G^(τt) be a weakly rigid family, where τ=σ̄t, and suppose every actual member X of G is weakly rigid. Its union U(x̄):=∃X(GX∧X(x̄)) is weakly rigid. For an actual U-instance choose a current G-member X witnessing it. Persistence of both G and X makes the instance necessary. For weak inextensibility, suppose every actual U-instance necessarily satisfies Z. For each actual G-member X, weak inextensibility of X gives X≤Z, i.e. □∀x̄(X(x̄)→Z(x̄)). Weak inextensibility of G applied to λX.∀x̄(X(x̄)→Z(x̄)) yields U≤Z.

If G is rigid and every actual member is rigid, then G≤Rigid: each current member necessarily satisfies the rigidity predicate, and weak inextensibility of G propagates that predicate. At every reached world the weak union lemma therefore applies, proving U rigid. This establishes rigid-family union closure without assuming necessary universal closure of the original membership premise by BF.

### Singleton-family coding

For a tuple ā of arguments of τ define its tuple haecceity δ_ā:=λx̄.∧_i(x_i=a_i). Define

    J(F)(X) := ∃ā(F(ā)∧X=δ_ā),     u(K)(ā):=∃X(KX∧X(ā)).

Here J maps τ-relations to relations of type τt; u maps τt-relations to τ-relations. The tuple haecceities are rigid C-theorematically. Direct images show that J preserves weak rigidity and rigidity. The union lemma shows that, for any K≤J(F), weak rigidity or rigidity of K passes to u(K), because all its members are necessarily tuple haecceities. C also proves

    u(J(F))=F;        K≤J(F) ⇒ J(u(K))=K.

The latter identity holds because at every world every member of K is a tuple haecceity, and a tuple belongs to its union precisely when its own haecceity is a member. All equalities are established necessarily, not by actual coextensivity alone. These identities also give preservation/reflection of containment under the corresponding maps.

Consequently:

* **TR_(τt) ⇒ TR_τ.** If F is weakly rigid then J(F) is weakly rigid, hence rigid by the higher Tame Rigidity instance. Its union F is rigid.
* **RP_(τt) ⇒ RP_τ.** If F is rigid then J(F) is rigid. The higher RP instance makes the family of rigid subrelations of J(F) rigid. Its direct image under u is exactly the family of rigid subrelations of F, by the two identities and closure lemmas. Direct images preserve rigidity, giving RP at F.
* **WRP_(τt) ⇒ WRP_τ.** The same proof uses weak rigidity throughout and the weak version of the union lemma. It does not infer necessity of weak rigidity of arbitrary old entities.
* **RC_(τt) ⇒ RC_τ.** Given F, take a rigid G actually coextensive with J(F). Its current members are tuple haecceities, hence rigid; the rigid union lemma gives a rigid u(G), actually coextensive with F.
* **WeakRC_(τt) ⇒ WeakRC_τ.** The analogous weak union proof suffices.

The subscript is the type of the relation F to which the principle applies, not the type of its arguments. These transfers include arbitrary nonempty argument tuples and the trivial nullary case. For example TR_((et)t) implies TR_(et); a failure at et therefore forces a failure at (et)t, then at ((et)t)t, and so on. No blanket claim is made that an arbitrary type lies on a common such chain with every other type.

## 18. Two exact, simpler descriptions of rigidity and its power gap

Proposed by the parent research agent and independently checked here, 22 October 2026. Direct source misc; novelty unchecked.

### Weak rigidity is reconstruction from actual singletons

Use the singleton family H_F=J(F) from §17. For every tuple ā and every Z of the relation type, C proves

    δ_ā≤Z iff □Z(ā).

The forward direction evaluates at the transported ā at every world. The reverse direction substitutes necessarily identical tuples; no ND is needed. Therefore, using the topic's existing order-theoretic LUB definition,

    WeaklyRigid(F) iff LUB(F,H_F),
    Rigid(F) iff □LUB(F,H_F).

Indeed, the upper-bound condition for F is ∀ā(F(ā)→□F(ā)), exactly weak persistence. The assertion that F is below every upper bound is ∀Z((∀ā(F(ā)→□Z(ā)))→F≤Z), exactly weak inextensibility. Conversely those two conditions are precisely the LUB biconditional. Rigidity is necessary weak rigidity, yielding the second displayed equivalence by necessitating the C equivalence.

This supplies an exact reading: a weakly rigid relation is the join of the haecceities of its current instances; a rigid relation continues to have that reconstruction at every accessible world. No Boolean Completeness is assumed: the particular join is asserted to exist and to be F itself. “Current instances” is indispensable; replacing them by a fixed original tuple set inside the later boxes would change the statement.

### The exact missing condition between TR+RP and WRP

Define the bounded propagation principle H by the schema

    ∀F [Rigid(F)→□∀X((WeaklyRigid(X)∧X≤F)→Rigid(X))].

It says that every future weakly rigid subrelation of an actual rigid bound is rigid. Then, over C,

    WRP iff TR + RP + H.

Forward: WRP implies TR and RP by the proved database arguments. For H fix an actual rigid F. WRP makes P_F(X):=WeaklyRigid(X)∧X≤F weakly rigid. In C weak rigidity implies full persistence, so □∀X(P_F(X)→□P_F(X)). Thus at every future world a weakly rigid X≤F is necessarily weakly rigid, i.e. rigid. This derivation of H at a fixed type uses only the WRP instance at that same type; it does not require Tame Rigidity at the higher property type.

Reverse: let F be weakly rigid. TR makes it rigid. RP makes R_F(X):=Rigid(X)∧X≤F rigid. H gives P_F≤R_F, while C gives R_F≤P_F. Necessary coextension identifies the two properties, so P_F is rigid and hence weakly rigid. This is WRP.

Thus the open TR+RP⇒WRP question is exactly whether those two principles force propagation of Tame Rigidity below actual rigid bounds. A countermodel merely having a new weak nonrigid relation in a future domain is insufficient: that relation must lie below the transported image of an actual rigid relation. The fixed-point cone does not meet this additional condition. This sharpens the target without treating the open implication as established.

## 19. Necessary distinctness supplies the bounded propagation missing from TR+RP

Original argument, Codex, 22 October 2026, independently checked in outline by the parent agent. Precise type scope: for a relation type τ=σ_1...σ_n t, assume unboxed ND only at its argument types σ_i. No ND at τ or τt, and no boxed ND, is needed. Then H_τ from §18 holds. In particular

    ND_(argument types of τ) + TR_τ + RP_τ ⇒ WRP_τ.

The all-type implication ND+TR+RP⇒WRP is not returned by the current proved-only Engine. This is a partial resolution of the unboxed TR+RP conjecture, not a proof without ND.

**Rigid products.** If F is rigid, so is F×F on pairs of argument tuples. Persistence is immediate. For weak inextensibility at any world, assume a test Z is necessary of every actual pair of F-tuples. For each actual first tuple ā, weak inextensibility of F in the second tuple gives □∀b̄(F(b̄)→Z(ā,b̄)). Apply weak inextensibility of F in the first tuple to λā.∀b̄(F(b̄)→Z(ā,b̄)). The result is (F×F)≤Z. The same proof works at every reached world since F is rigid.

**Distinctness inside a rigid bound propagates.** Write ND_F for ∀āb̄(F(ā)∧F(b̄)∧ā≠b̄→□(ā≠b̄)). Coordinate ND gives this at the evaluation point. Every current F-pair satisfies D(ā,b̄):=□(ā=b̄)∨□(ā≠b̄): use NI for equality and ND_F for inequality. D is persistent by 4. Weak inextensibility of the rigid product gives (F×F)≤D. Thus necessarily every pair in F has its equality decided, and in particular □ND_F. This step replaces a forbidden appeal to BF; no universal is simply moved under a box.

**A weak subrelation of a distinctly separated rigid bound is rigid.** Work at any world where F is rigid and ND_F holds. Let X be weakly rigid with X≤F. Fix a current F-tuple ā. If X(ā), weak persistence gives □X(ā). If ¬X(ā), every current X-tuple b̄ lies in F and differs from ā; ND_F therefore gives □(b̄≠ā). Apply weak inextensibility of X to λb̄.b̄≠ā. It gives X≤λb̄.b̄≠ā, hence □¬X(ā). Thus each current F-tuple satisfies D_X(ā):=□X(ā)∨□¬X(ā). This predicate is persistent by 4, so weak inextensibility of F gives

    □∀ā(F(ā)→D_X(ā)).

At any later world let Z be a test necessarily true of every current X-tuple. For each current F-tuple ā, either X(ā), giving □Z(ā), or ¬X(ā), giving □¬X(ā) by the displayed decision property. Either way □(X(ā)→Z(ā)). Weak inextensibility of F at that later world yields F≤λā.(X(ā)→Z(ā)); since X≤F remains true, X≤Z. Therefore X is weakly inextensible at every later world. It is already persistent, as every weakly rigid relation is. Hence it is rigid.

Start now at the original world with an arbitrary rigid F. The first lemma makes ND_F necessary from the unboxed argument-type ND assumptions. The second lemma consequently applies at every future world to every weakly rigid X≤F there. This is H_τ. Combine with the exact §18 decomposition to obtain the displayed WRP implication.

A further exact improvement of definitions, independently proposed by the parent: under ND at the argument types, BC_τ gives WeakRC_τ directly. For an arbitrary X, choose by BC a join G of its actual tuple-haecceity family H_X. If X(ā), δ_ā≤G gives G(ā). If ¬X(ā), ND makes each actual X-tuple necessarily distinct from ā, so every member of H_X lies below ¬δ_ā; the join does too, giving ¬G(ā). Thus G and X are actually coextensive. Their current haecceity families therefore have the same current members, so G is also the join of H_G and hence weakly rigid by §18. The all-type ND+BC⇒WeakRC implication is ALREADY DERIVED in the database (ND→Vicinity; BC→weak inextensible comprehension; their conjunction→Actuality; BC+Actuality→WeakRC). The value of this argument is its simpler proof and exact per-instance assumption localization, not a new schema arrow.

## 20. Two further equivalent readings of an individual BF instance

This is a sharper per-instance formulation of a KNOWN schema equivalence: the map already has BF⇒Functionality⇒Tractarianism⇒BF, sourced to Bacon–Dorr, Proposition 2.1 n.27 pp.20–21. No claim of a new all-type implication is made.

For any argument type σ and ANY admitted relational output type τ≠e,

    BF_σ iff Functionality_(σ,τ).

Forward: pointwise equality of f,g gives ∀x□(f(x)=g(x)) by NI. BF_σ gives □∀x(f(x)=g(x)). At each reached world these identities imply truth agreement on all remaining arguments of τ. Intensionality then gives f=g. No BF at those remaining argument types is needed: their universal closure is made inside the already obtained box using identity at that world.

Reverse: embed propositions as constant τ-relations c(p):=λȳ.p. Given ∀x□P(x), the operations x↦c(P(x)) and x↦top_τ agree on every current x. Functionality makes them identical. Applying their necessary identity at arbitrary future arguments gives □∀xP(x), namely BF_σ. Nonempty argument domains supply a tuple when τ is nonnullary; the empty tuple is immediate.

Equivalently BF_σ says that, for every X^σt, ∀xX(x) is the Boolean greatest lower bound of its CURRENT instances {X(a):a actual}; dually ∃xX(x) is their least upper bound. C already supplies the ordinary bound direction. The missing greatest/least condition is precisely Tractarianism_σ and its dual. This explains BF as agreement between quantification and the Boolean order, without assuming Boolean Completeness or claiming that the future domain is literally constant in an arbitrary presentation.

## 21. A small dense basis reduces Boolean Completeness to restricted completeness

Suggested by the parent and independently audited here, 22 October 2026. This is an elementary Boolean-algebra theorem applied to the admitted Boolean algebra at a fixed relational type τ; novelty is not claimed without a source search. Source category misc for this derivation.

Let D be an admitted family of τ-entities that is order-dense among nonzero elements:

    ∀z (z≠bottom → ∃d(Dd ∧ d≠bottom ∧ d≤z)).

Assume every admitted subfamily of D has a least upper bound. Then BC_τ holds. Given an arbitrary admitted family X, form the admitted subfamily

    D_X(d) := Dd ∧ ∃x(Xx ∧ d≤x),

and let u be its join. If an actual member x of X were not below u, then x∧¬u would be nonzero. Density supplies a nonzero d∈D below x∧¬u. Since d≤x, it belongs to D_X and hence lies below u, contradiction. Thus u is an upper bound of X. Every upper bound of X bounds each member of D_X and therefore bounds u, proving that u is the join of X.

Consequently, if D is κ-countable in any adopted sense for which admitted subfamilies inherit κ-countability, and CBC_(κ,τ) asserts that every admitted κ-countable family at τ has a join, then

    κ-countable order-dense family at τ + CBC_(κ,τ) ⇒ BC_τ.

There is no choice principle: D_X is obtained by comprehension, and the proof never selects a witness d for each z simultaneously. If Atomicity_τ holds, the family of atoms is order-dense, so κ-countability of that atom family gives the parent's special case. The exact internal definition of κ-countability must be specified before introducing a database principle; the argument above isolates the only inheritance property used.

## 22. Uniform rigidification is exactly the ND strengthening of comprehension

Original formulation/argument, Codex, 22 October 2026. No database edit; source category misc and literature novelty unchecked. An operation output must be relational, so the construction uses only admitted types.

For a fixed relational type τ define UniformWeakRC_τ by existence of an operation R^(ττ) such that every actual X^τ has R(X) weakly rigid and actually coextensive with X. Define UniformRC_τ similarly with rigid in place of weakly rigid. These strengthen the respective comprehension instances by requiring a single admitted operation to select the coextensions. Selection is unique: C proves that coextensive weakly rigid relations are identical.

**Even one uniform instance gives Boolean evaluation.** For a proposition p put c(p):=λx̄.p at type τ. Fix one actual argument tuple ā; when τ=t use the empty tuple. Let U=R(top_τ) and define E(p):=R(c(p))(ā). If p is true, c(p) and top_τ are actually coextensive, so their weakly rigid representatives are identical by uniqueness. Thus E(p)=U(ā); U is actually universal and weakly persistent, so U(ā)=top. If p is false, c(p) is actually empty, and its weakly rigid representative is bottom_τ, giving E(p)=bottom. Consequently

    ∃E^(tt) ∀p [(p→E(p)=top) ∧ (¬p→E(p)=bottom)].

This is the Boolean-evaluation principle developed by the parent, equivalent over C to ND+Actuality. Thus UniformWeakRC at ANY one relational type, and hence UniformRC there, already implies full all-type ND and Actuality, not just distinctness of that relation's arguments.

For completeness the ND consequence of Boolean evaluation has a direct short proof. E(top)=top. For any current distinct a,b at any type, p:=(a=b) is false, so E(p)=bottom. Both identities are necessary by NI. At any future world with a=b, p=top by NI and the definition of □, so congruence gives E(p)=E(top), contradiction. Hence □a≠b.

**Exact all-schema equivalences.** In the reverse direction, ND+WeakRC implies Plenitude by the recorded Bacon–Dorr Proposition 2.16 argument (with its independently recorded weakening to WeakRC). At each τ the relation

    V(X,Y) := WeaklyRigid(Y) ∧ coext(X,Y)

is total and single-valued by WeakRC and coextensive-WR uniqueness. Plenitude represents it by an admitted operation R:τ→τ. Replacing WeaklyRigid by Rigid proves the rigid case. Therefore, as all-type schemata,

    UniformWeakRC iff ND + WeakRC,
    UniformRC iff ND + RC.

No converse from merely ND+the single instance WeakRC_τ or RC_τ is claimed: the available Plenitude proof uses the all-schema comprehension assumptions (or appropriate additional instances).

**Boolean retraction refinement.** Under either uniform schema, R is an actual retraction onto the weakly rigid or rigid relations, respectively: R(Y)=Y whenever Y has the specified rigidity, and R(R(X))=R(X). It fixes bottom, and its image lies below U=R(top), since every current member of any weakly rigid Y necessarily belongs to U, so WI(Y) gives Y≤U.

Under ND, finite intersections and relative differences of weakly rigid relations are weakly rigid. To see this, a false current B(ā), for weakly rigid B, implies □¬B(ā): each actual B-tuple differs from ā necessarily, and WI(B) applies to its complement haecceity. For A∩B, a test necessary on its current members is therefore necessarily implied by B at every current A-tuple; WI(A) gives the required upper bound. For A\B the same argument interchanges the decided B-cases; weak persistence uses the just-proved stability of false B-membership. Finite unions are weakly rigid without ND by the union lemma. For rigid relations the corresponding closure under ND was independently established in the rigidity lane by propagating membership decisions over the rigid bound.

Uniqueness of representatives now yields, for all actual X,Y,

    R(X∨Y)=R(X)∨R(Y),
    R(X∧Y)=R(X)∧R(Y),
    R(¬X)=U\R(X),     R(bottom)=bottom.

Thus the canonical operation is a Boolean-algebra retraction onto the (weakly) rigid relations, with U as its unit. These equations are identities and hence necessary for each fixed actual pair of arguments. No BF is used to box their universal closure; the behavior of R on genuinely new future arguments remains unrestricted by this reasoning.

## 23. Tame Rigidity is closure of rigid relations under existing joins

Original argument, Codex, 22 October 2026. Direct source misc; novelty unchecked. Fix a relational type τ. Families below are admitted, and every assertion about their members quantifies over current members. The family itself need not be weakly rigid, rigid, finite, or countable.

**Existing joins preserve weak rigidity in C.** Suppose Z is a Boolean least upper bound of H and every current H-member Y is weakly rigid. First show persistence of Z. Each such Y is persistent and Y≤Z. Consequently Y≤λā.□Z(ā): at any reached world, membership in Y remains true at every later world, where Y≤Z remains available. The least-upper-bound property therefore gives Z≤λā.□Z(ā), exactly persistence.

For weak inextensibility, let a test W be necessary of every current Z-instance. Since Y≤Z, it is necessary of every current Y-instance, for each current H-member Y. Weak inextensibility of Y gives Y≤W. The least-upper-bound property gives Z≤W. Thus Z is weakly rigid.

In fact the weak-inextensibility half alone is closed under existing joins, while the persistence argument separately shows closure of persistent relations under existing joins. Their conjunction yields the displayed weak-rigidity closure.

It follows that

    TR_τ iff every existing Boolean join of a current family of rigid τ-relations is rigid.

Forward: the preceding C lemma makes such a join weakly rigid, and TR makes it rigid. Reverse: a weakly rigid F is the existing join of its family of current tuple haecceities, by §18. Those haecceities are all rigid. The asserted join closure therefore makes F rigid.

This is an exact reformulation with no Boolean Completeness premise. Under BC it becomes ordinary closure of the rigid fragment under all admitted joins. It explains precisely why finite rigid union closure is a theorem while arbitrary rigid join closure can fail: the latter is Tame Rigidity itself.

**Canonical representatives turn current unions into Boolean joins.** Whenever each relation at τ has a weakly rigid coextension, let r(X) denote its unique coextension (an operation is not needed for this sentence). For an admitted family H put V(ā):=∃X(HX∧X(ā)). Then r(V) is the Boolean join of the current representatives r(X), HX. Each r(X) is below r(V), by weak inextensibility and the latter's persistence. If W bounds every current r(X), each current V-instance belongs to a current X and hence necessarily satisfies W. Weak inextensibility of r(V) gives r(V)≤W. If the representatives are rigid instead, the same proof makes the join rigid. This formulation requires the image family to be admitted when it is written as a standalone family; under the uniform operations of §22 it is admitted by comprehension.

## 24. ND plus Rigid Comprehension implies Weakly Rigid Power

Original argument, Codex, 22 October 2026. Sent to the parent for independent audit. No record edit; source category misc, literature novelty unchecked. This section supplies a proof of the previously unrecorded implication, not a claim of the unrestricted TR+RP conjecture.

**Precise local assumptions.** For τ=σ̄t it suffices to assume ND at the argument types σ_i, ND at t, and RC at the property type τt. These imply RP_τ and WRP_τ. In particular, all-schema ND+RC implies all-schema WRP.

**1. Distinctness inside F is necessary.** For a rigid F, argument-type ND implies □ND_F by §19: F×F is rigid and its current pairs have equality decided; WI(F×F) propagates that persistent decision predicate. Thus at every reached world distinct tuples of F remain distinct.

**2. Rigid subrelations of F have necessary distinctness.** Work at any such world and take distinct rigid X,Y≤F. They cannot be actually coextensive, because coextensive weakly rigid relations are identical. Choose a current tuple ā where their membership differs, say X(ā) and ¬Y(ā). It lies in F. Positive X-membership is necessary. Every current Y-tuple lies in F and differs from ā, hence necessarily differs by ND_F. WI(Y) gives □¬Y(ā). Consequently □X≠Y. The argument applies at every reached world: the family R_F(X):=Rigid(X)∧X≤F has necessarily separated members.

**3. A rigid representative of R_F cannot acquire a new rigid member.** By RC_(τt) choose a rigid G currently coextensive with R_F. Every current G-member necessarily satisfies R_F: both rigidity and containment in F are persistent. WI(G) therefore gives G≤R_F.

At any reached world suppose R_F(Y) and ¬G(Y). Every current G-member X satisfies R_F(X) and differs from Y. Step 2 gives □X≠Y. WI(G), applied to λX.X≠Y, yields □¬G(Y). Since R_F(Y) is itself necessary, this witness Y remains a witness to

    q := ∃Y(R_F(Y)∧¬G(Y))

at every later world. Thus □(q→□q): q is a persistent proposition.

**4. ND_t forbids this new persistent truth.** Current coextensivity of G and R_F gives ¬q. In particular q≠top. ND_t gives □(q≠top), i.e. □¬□q. Together with □(q→□q) this yields □¬q. Hence R_F≤G. The reverse containment was proved in step 3, so R_F=G and R_F is rigid. This is RP at the arbitrary rigid F.

For WRP_τ, RC_(τt) implies RC_τ by singleton-family coding and union (§17), so TR_τ holds. The argument-type ND assumptions give bounded propagation H_τ by §19. The exact decomposition WRP iff TR+RP+H (§18) then gives WRP_τ.

Equivalently one can use H directly: every future weakly rigid subrelation of an actual rigid F is rigid, so its weak-power family is identical to the rigid-power family just proved rigid. An arbitrary current weak F is rigid by RC_τ.

**Modal principle isolated.** The final step uses only the elementary fact that, under ND_t, a currently false persistent proposition cannot become true. If p is false, p≠top and ND_t makes this necessary; persistence would turn any future p into □p, contradiction. No BF or illicit boxing of ND or RC is involved.
