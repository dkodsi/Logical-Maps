# Mixing, uniform witnesses, and supported Henkin models

Research notes, 22 October 2026. Original arguments developed in this research chat; the finite/cofinite exact-configuration construction was proposed by the parent research chat and audited here. These notes are not database records, published results, claims of literature novelty, or a Lean verification. No published/human-authored records were changed. All model constructions below use ordinary ZFC in the metatheory unless specified otherwise.

## 1. Fixed base and recorded evidence

Write B = C + □Plenitude, in the fixed relational type system (types e,t, and σ→τ only for τ≠e). The boxed premise is essential. The proved records identify B with C + □ND + Atomicity, not C + unboxed ND + Atomicity.

A proved-only `scripts.pmap.load_topic`/`Engine` query, with □Plenitude in the queried premises and no optional engine background, returned these recorded consequences: □Barcan, □Rigid Comprehension, □Boolean Completeness, □Strong Leibniz, and No Pure Contingency. Relevant records include `c5-and-atomicity-imply-necessary-plenitude`, `c5-and-atomicity-imply-necessary-rigid-comprehension`, `c5-and-atomicity-imply-no-pure-contingency`, and the necessary-Plenitude implications. Identity necessity and converse Barcan are already C theorems. Source background: Bacon–Dorr, Classicism, 16 May 2023 draft, §§2.2–2.3, pp. 23–34, and §3.5, pp. 58–61. These citations support the recorded framework/consequences, not the original constructions below.

The engine also found recorded B-models failing Intensional Choice and Relational Choice, notably choiceless full S5 variants. Sections 3–5 below supply direct Henkin separations in ZFC instead.

For a relational type τ=α₁…αₙt, define current coextension

    R ≈τ S  :=  ∀z₁…zₙ (R[z₁,…,zₙ] ↔ S[z₁,…,zₙ]).

The tuple may be empty: at t, this is R↔S. This is local coextension, not identity of intensions.

## 2. General supported-hierarchy construction

Let G act on nonempty sets W (worlds) and E (individuals). Let F be an upward-closed, conjugation-invariant filter of subgroups, closed under finite intersections. Assume Stab(w)∈F for each w∈W and Stab(e)∈F for each e∈E. A G-object is supported when its stabilizer belongs to F.

Define recursively:

* D_e=E.
* D_t={A⊆W : A is supported}, with image action gA.
* D_{στ} is the set of supported functions D_σ→D_τ, acted on by conjugation: (gf)(x)=g(f(g⁻¹x)).

All type domains are sets and are G-invariant. Interpret application as function application, equality as actual equality, and a proposition A as true at w iff w∈A. Thus □A holds iff A=W. Quantifiers range over the fixed typed domains at every world.

### 2.1 Comprehension, lambda closure, and C

For any formula with finitely many assigned free parameters, intersect their stabilizers. Induction on formulas shows

    g⟦φ⟧_a = ⟦φ⟧_{ga}.

Boolean operations preserve this equivariance. Quantification preserves it because every domain is invariant and g bijects the quantified domain. Equality and application are equivariant. Therefore the truth set of a formula is supported by the common stabilizer of its parameters and belongs to D_t.

The denotation x↦⟦T⟧_{a[x:=x]} of a lambda abstraction is equivariant under that same common stabilizer, hence belongs to the appropriate function domain. Its values belong to the target domain by induction. This proves full comprehension and lambda closure for the language, including quantification over all admitted higher types.

The usual classical typed Henkin interpretation validates H, beta/eta, and the logical operations. H-equivalent formulas have the same truth sets under every assignment; their lambda abstractions therefore denote the same functions. Thus Logical Equivalence, with its theoremhood restriction, is valid. This verifies C; it is not an appeal to closure of only a fragment of formulas.

### 2.2 Atomicity at every relational type

Flatten τ=α₁…αₙt. Each object X determines a subset of W×D_{α₁}×…×D_{αₙ}. If X is nonzero, choose (w,a₁,…,aₙ) in that subset. Its singleton relation δ is supported by

    Stab(w) ∩ Stab(a₁) ∩ … ∩ Stab(aₙ),

which belongs to F. Curried sections of δ are supported too, so δ belongs to D_τ. It is an atom in the full powerset Boolean algebra and hence in the restricted algebra. It lies below X. This proves all-type Atomicity. Equality is global actual equality, so □ND holds. The recorded equivalence consequently proves B.

### 2.3 Direct verification of □Plenitude

There is also a direct check. Let U∈D_{σ τ t}, τ≠e, be functional at a world w. Define f(x) as the unique y with U(x,y) true at w. This uses unique specification, not choice. For

    H=Stab(U)∩Stab(w)∈F,

uniqueness and equivariance give f(hx)=h f(x) for h∈H. Hence f is supported, belongs to D_{στ}, and represents U at w. This works at every w, giving □Plenitude directly.

### 2.4 Exact criterion for supported interworld selectors

For F₀∈D_{σt}, a selector G₀≤F₀ necessarily uniquely instantiated is exactly the graph of a supported map f:W→D_σ with f(w)∈(F₀)_w. If H∈F supports F₀, an H-equivariant selector exists iff, for one representative w of every H-orbit on W, the fibre (F₀)_w has a point fixed by H∩Stab(w).

Necessity: equivariance forces f(w) fixed by every element fixing w. Sufficiency: in ZFC choose orbit representatives and suitable fixed points a_w, and define f(hw)=ha_w. The fixed-point requirement makes this independent of the representative h. Equivariance gives support H. A supported selector need not use the original support of F₀, but intersecting its support with that of F₀ yields an allowed common H.

This is a model-theoretic characterization, not an additional object-language axiom.

## 3. Pair-individual models and the exact world-size threshold

Fix an infinite regular cardinal κ and a set J with |J|≥κ. Put E=J×{0,1}; let G=(Z/2Z)^J independently flip the pairs. Let H_S be the subgroup fixing both members of each pair indexed by S, and let F be generated by H_S for |S|<κ. Let W be any nonempty set on which G acts trivially. Use the hierarchy in §2.

D_t=P(W), and the G-action at t is trivial. Induction shows that every e-free type (built only from t) has its ordinary full function domain and trivial G-action. In particular, all interworld-choice instances at e-free types hold in ZFC.

### 3.1 If |W|<κ, Intensional Choice holds at every type

Let F₀∈D_{σt} be necessarily instantiated. Externally choose a_w∈D_σ with F₀(a_w) true at w, and for each a_w choose a support S_w of size <κ. Regularity gives |⋃_{w∈W}S_w|<κ. Define

    G₀(x)={w∈W : x=a_w}.

The subgroup fixing the union fixes every a_w, hence fixes G₀. Therefore G₀ belongs to D_{σt}, is below F₀, and is necessarily uniquely instantiated. This works for every type σ. The use of metatheoretic AC is legitimate: the construction is an ordinary ZFC Henkin countermodel to an internal choice principle.

### 3.2 If |W|≥κ, Intensional Choice at e fails

Choose a surjection ρ:W→κ and an injection i:κ→J. Define F₀(x) true at w exactly when x belongs to pair i(ρ(w)). F₀ has empty support, since pair flips preserve pair membership. It is necessarily inhabited.

If a selecting G₀ had support S of size <κ, choose α with i(α)∉S, and w with ρ(w)=α. Flipping pair i(α) fixes w and G₀ but interchanges the only two eligible objects. Thus it carries the unique selected object to a different selected object, contradiction.

Consequently, for this model family, the all-type Intensional Choice schema holds exactly when |W|<κ.

### 3.3 Relational Choice fails for every nonempty W

For each j let P_j∈D_{et} be the rigid predicate of pair {j}×{0,1}. Each P_j has empty support. Define a rigid relation U^{(et)et} by

    U(P,y) iff [P=P_j for some j implies P(y)].

More explicitly: when P is a pair predicate, its candidates are that pair; otherwise all individuals are candidates. This is an equivariant serial relation, hence admitted. If S were a functional subrelation at any world w, let A, |A|<κ, support S. Choose j∉A. Flipping pair j fixes S, w, and the input P_j, but swaps its only two permissible outputs. Functionality is impossible.

Thus B+Intensional Choice does not imply Relational Choice, even with infinitely many worlds and a full external propositional powerset. A concrete choice is κ=ω₁, J=ω₁, W=ω. This establishes strictness in ZFC, without assuming that AC fails in the metatheory.

The same family with κ=ω, J=W=ω has B and all e-free Intensional Choice instances, but fails Intensional Choice at e. It therefore separates propositional interworld choice from individual interworld choice.

## 4. Pair-world model: the converse type separation

Let W=ω×{0,1}, with P_n={n}×{0,1}; let E be a singleton. Let G independently flip the world pairs, and use finite supports in the pair indices. Every world has singleton-index support, so §2 applies and proves B. Here D_t consists of arbitrary unions of whole pairs, with arbitrary splits in finitely many pairs.

Intensional Choice at e holds trivially, since the individual domain is a singleton.

For p∈D_t define F₀(p)=P_n when p is a singleton proposition of a member of P_{n+1}; put F₀(p)=∅ otherwise. This is an equivariant function D_t→D_t, hence an admitted property of propositions. At a world in P_n its only candidates are the two singleton propositions of P_{n+1}. It is necessarily inhabited.

If G₀≤F₀ selected uniquely everywhere, choose a finite support A for G₀ and n with n+1∉A. At w∈P_n, flipping P_{n+1} fixes w and G₀ but interchanges the only two eligible singleton propositions. Contradiction.

Hence over B, Intensional Choice at e and Intensional Choice at t are independent. The positive side for t in §3 is stronger: all e-free instances hold. These are genuine additional principles, not unboxed/boxed artifacts; the constructions validate the indicated facts at every world.

## 5. Definition audit: choice as local-to-global witnessing

The following are equivalent formulations, not new claims of independent strength. They distinguish relation extensions, which may be pasted, from identity of intensional objects, which may not be pasted indiscriminately.

### 5.1 Local-to-global existence for extensional properties

For Φ^{τt}, τ relational, put

    Ext_τ(Φ) := ∀R,S (R≈τS → (ΦR↔ΦS)).

Consider the schema

    [□Ext_τ(Φ) ∧ □∃R^τ ΦR] → ∃R^τ □ΦR.             (LG)

Close Φ universally. Type variables remain metalinguistic. **Over C, the full LG schema is equivalent to the full Intensional Choice schema.**

IC⇒LG: Apply IC to Φ, obtaining a property H of candidates, necessarily uniquely instantiated and below Φ. For τ=ᾱt define

    M[ā] := ∃R (HR ∧ R[ā]).

At each world there is exactly one H-candidate R, and M is coextensive there with R. Necessary extension-invariance of Φ therefore gives ΦM at every world.

LG⇒IC: Given F^{σt}, define a property of R^{σt} saying that R is a singleton subproperty of F:

    Θ_F(R) := [∀x(Rx→Fx)] ∧ ∃x[Rx ∧ ∀y(Ry→y=x)].

This is extension-invariant in R at each world. Whenever F is instantiated, λy(y=x) supplies such an R. Thus □∃x Fx gives □∃R Θ_F(R). LG produces an R satisfying Θ_F necessarily, exactly the required intensional selector.

**Type caveat:** this is equivalence of full schemas. The reverse shifts the target to σt. It is false to claim without further argument that LG at τ is equivalent to IC at τ. In fact LG at t is already a C theorem: take q:=Φ⊤; at each world use local extensionality and the existence of a Φ-witness to show Φq.

Suggested plain name: “Extensional Witnessing.” “Local-to-global existence for extensional properties” is longer but immediately explanatory.

### 5.2 Uniform extensional Skolem functions

For Φ^{σ τ t}, τ relational, consider

    [□∀x∃R Φ(x,R)
       ∧ □∀x,R,S (R≈τS → (Φ(x,R)↔Φ(x,S)))]
       → ∃F^{στ} □∀x Φ(x,Fx).                     (US)

Close Φ universally. **Over C, the full US schema is equivalent to the recorded Modalized Relational Choice schema.**

MRC⇒US: choose S^{σ τ t} necessarily functional and below Φ. Put

    F[x,ā] := ∃R(S(x,R) ∧ R[ā]).

At every world and input x, Fx is coextensive with the unique selected candidate R. Extension-invariance gives Φ(x,Fx).

US⇒MRC: For a necessarily serial U^{σρt}, use output type τ=ρt and let Φ(x,R) say “R is a singleton subproperty of the U-row at x.” The local singleton argument above verifies the premise; the operation F^{σρt} supplied by US is itself the desired necessarily functional subrelation of U.

Over B, these are also equivalent to Relational Choice, Functional Choice, and □Functional Choice. The nontrivial recorded steps are: B gives BF, weak rigid comprehension, Atomicity, and No Pure Contingency; with RC the first three give IC (`bf-weak-rigid-comprehension-atomicity-and-relational-choice-imply-intensional-choice`); pure noncontingency boxes RC; □RC+IC gives MRC (`necessary-relational-choice-and-intensional-choice-imply-modalized-relational-choice`). Conversely MRC implies RC already over C: replace a serial U by U'(x,y):=(Serial(U)→U(x,y)), which is necessarily serial. Plenitude plus RC is Functional Choice; pure noncontingency boxes its closed instances.

Suggested plain name: “Uniform Extensional Choice.” This explains □Functional Choice as simultaneous selection of admissible extensions across inputs and worlds. It does not license selection of a single rigid object equal to different local objects.

### 5.3 Choice indexed by worlds

Over B, IC at a fixed type σ is equivalent to relational choice restricted to rigid families indexed by proposition atoms. Formally, every rigid U^{tσt} with a nonempty row at each proposition atom has a rigid S which is uniquely instantiated on each atom-row and is contained there in U. Nonatom rows can be ignored or set empty.

The translation of an arbitrary interworld family F is

    U(a,x) := Atom(a) ∧ □(a→Fx).

At a possible atom a, □∃x Fx ensures a candidate x with □(a→Fx). To see this without choosing a witness at an inaccessible point: if no such x existed, atom-decision gives ∀x□(a→¬Fx); BF gives □(a→∀x¬Fx), contradicting possibility of a and □∃x Fx. For uniqueness, two selected x,y under a force a≤(x=y); rigid identity and possibility of a imply x=y. The base's strong-world and rigid-comprehension results justify these constant-domain readings.

Recover an interworld selector from a selected rigid atom-indexed relation S by

    Gx := ∃a(Atom(a) ∧ a ∧ S(a,x)).

There is exactly one true proposition atom at each world. Conversely, translate a rigid atom-indexed U to F(x):=∃a(Atom(a)∧a∧U(a,x)), apply IC, and encode its selected G by the displayed U-construction. The maps preserve the rows because a rigid relation has the same extension at every world. This is the type-local counterpart of the full-schema characterizations above.

Suggested plain name: “Choice over Worlds.” It makes the strict separation in §3 transparent: choosing over W need not amount to choosing over every typed domain.

## 6. Exact configuration models and the role of uniqueness

This section gives a finite/cofinite construction.

Let E be infinite, G=Sym(E), and W=FinCof(E), the set of finite and cofinite subsets, with its natural image action. Use the finite-support filter. Every w∈W has finite support (itself or its finite complement), so §2 verifies B.

Define R∈D_et by

    R(x)={w∈W : x∈w}.

This is equivariant. A rigid individual predicate corresponds precisely to a supported subset of E. Under the full permutation group with finite supports those subsets are exactly the finite/cofinite ones: outside a finite support all individuals lie in a single orbit, so the subset either contains all of them or none. Thus the worlds realize every rigid individual extension, and realize it exactly once. The slice at world w is w itself.

Nevertheless IC at e fails. Let F(x) hold at a two-element world w iff x∈w, and at every other world let all individuals be eligible. This F is equivariant and necessarily inhabited. For any finite support A of an alleged selector, take w={a,b} disjoint from A. The transposition (a b) fixes w and the selector but swaps every eligible candidate. RC with target e also fails by the same transposition argument applied to unordered-pair predicate codes.

### 6.1 Exact configurations plus interworld choice

Over B, suppose a relation R realizes each rigid individual extension at exactly one proposition atom. Then IC_e implies Relational Choice with target e and arbitrary input type σ.

Given a serial U^{σet} at the evaluation point, use Rigid Comprehension to obtain a rigid coextensive U*. Its rows X_x are rigid nonempty subsets. Each X_x has a unique realizing atom a_x. Apply IC_e to the necessarily inhabited property “choose an R-instance if R has an instance, otherwise any individual.” Encode the resulting selector as a rigid atom-indexed relation S(a,y). Define

    T(x,y) iff ∃a [a is the realizing atom of X_x ∧ S(a,y)].

The realizing atom is unique, its R-extension is nonempty, and S chooses exactly one element of it. Therefore T is a functional subrelation of U* and, at the evaluation point, of U. No operation returning an individual is required.

The converse follows from §5.3: arbitrary-input relational choice with target e includes world-index choice. Thus, under exact configuration realization, IC_e and RC with target e are equivalent. The finite/cofinite model shows that exact realization by itself supplies neither.

**Unresolved:** the same argument does not establish the result from mere surjective realization with repeated profiles. Different realizing worlds may yield different selected individuals. No claim of equivalence or separation for that weaker premise is made here.

## 7. Infinitary extensions: specify the parameter rule

These statements concern explicitly stronger languages, not unannounced changes to C. Permit countable conjunction/disjunction in formula bodies, including lambda bodies; use their ordinary truth-set semantics, the corresponding introduction/elimination rules, and retain theoremhood restrictions on necessitation and Logical Equivalence. No completeness claim about an infinitary proof system is needed.

### 7.1 A common finite parameter set

Every supported hierarchy in §2 remains a model when infinitary formulas have a common finite set of free parameters and no unbounded family of independently supported named constants. Inductively the entire formula is equivariant under the common stabilizer of those parameters; arbitrary intersections/unions of truth sets sharing that stabilizer are supported by it. Quantifiers remain equivariant. This works semantically even for arbitrary set-sized well-founded conjunctions sharing that finite parameter set.

Thus such infinitary comprehension does not restore either IC or RC: the finite-support countermodels still apply.

### 7.2 Countably many independent parameters

The finite-support models need not validate this stronger rule. In the pair-individual model introduce parameters c_n=(n,0). The formula

    ⋁_{n<ω} x=c_n

defines one member of every pair, so its lambda abstraction has no finite support. Treating these as infinitely many named constants does not remove the problem: their interpretations still have an unbounded union of supports.

However the countable-support construction κ=ω₁, J=ω₁, W=ω validates countable conjunctions and lambda-comprehension with countably many independent parameters. The union of their countable supports is countable. That model has every IC instance and still fails RC on the ω₁-indexed pair codes.

More generally, with regular κ and supports of size <κ, formulas using <κ independent parameters and <κ conjunctions are handled by unions of <κ supports (with the standard size bounds at each formula). Any infinite-parameter universal closures or quantifier blocks must be specified as part of the new language; the original finite relational type system need not be changed.

Therefore neither the common-finite-parameter nor the countable-parameter infinitary strengthening, as specified, forces general Functional Choice. This is a semantic separation, not a claim that all conceivable infinitary extensions behave alike.

## 8. Guardrails and remaining work

* Internal pasting of already supplied compatible relation extensions is definable by existential union and is not a new choice axiom. The substantive principles concern obtaining witnesses.
* Exact identity-pasting of arbitrary objects is different and conflicts with rigid identity when the local identities disagree.
* Full internal representation never means every external family is admitted. A countable elementary substructure of a full infinite S5 structure (with explicit world/evaluation sorts) preserves each internal C/choice schema but has countably many propositions over countably many atom-worlds, hence cannot contain every external subset. A complete write-up should specify the many-sorted elementary-substructure language; this is a separate caveat, not needed for the explicit support models.
* Definitions in §5 are replacements/equivalent presentations only under their stated assumptions. The type-local restrictions in §4 are genuinely weaker and independent.
* No claim of literature novelty has been checked. Original proofs should be recorded under `misc`, not attributed to the cited Classicism pages.
* No database/generated/Lean files were changed; no Lean work was performed.

## 9. A sharply restricted witness principle already excluded by Maximalism

Let

    F_x(y) := (∃z z≠x) → y≠x,
    Alt(x,G) := G≤F_x ∧ □∃!y Gy.

The recorded result `maximalism-incompatible-with-intensional-choice` (Cian Dorr, 16 October 2026; model consistency verification recorded there) uses only this family, at type e. Its consistent pure sentence is

    Q := ∃a [∀z(z=a) ∧ ¬∃G Alt(a,G)].

The witness is the recorded symmetry-constrained full model with a one-point object and all maps to three individuals. No new assertion about that source model is needed here.

A strengthening of the recorded deduction is immediate: **C plus Pure Maximalism entails ¬∃x,G Alt(x,G).** Suppose Alt(x,G). Both its conjuncts are necessary by 4. Pure Maximalism in its possibility form gives ◇Q. At a Q-world, x is identical to the sole individual a, so the persistent witness G satisfies Alt(a,G), contradicting Q. This argument needs only one alternative selector, not IC for every property or even IC for every x in this special family.

The extensional-witnessing instance Θ_{F_x} from §5.1 necessarily has local witnesses in C, since F_x is necessarily inhabited. Thus even its existentially weakened local-to-global conclusion is excluded by Pure Maximalism. This is a concrete comparison, not a proof that Maximalism is the weakest consistent extension under implication.

**Important calibration:** B already proves ∀x∃G Alt(x,G), without Functional Choice. Fix x. If some y≠x, ND gives □y≠x, and the haecceity of y is a suitable G. If no such y exists, ∀y(y=x); NI plus BF gives □∀y(y=x), so the haecceity of x is suitable. Therefore this sharp obstruction distinguishes Maximalism from B, but does not establish a new difference between B and B+□Functional Choice.

No conclusion about Maximalism versus IC at type t alone has been established by these arguments. The converse type-separation models in §4 do not resolve that question, since they satisfy B rather than Maximalism.

## 10. Which witness problems already glue in C?

This section further separates equivalent definitions from genuine strengthenings. It concerns pointwise current extensions, not algebraic meets of intensions; no Boolean Completeness premise is silently used.

### 10.1 Unique extension

Suppose Φ is necessarily extension-invariant, necessarily has a witness, and necessarily any two Φ-witnesses are coextensive. Then C proves ∃M□ΦM without IC. Define

    M[ā] := ∃R(ΦR ∧ R[ā]).

At each world, choose a Φ-witness for the local argument. All witnesses have its extension, so M is coextensive with it; extension-invariance yields ΦM. The proof uses local existential elimination and a single definable M, not a choice of a global family of witnesses.

### 10.2 Monotone solution classes

If Φ is necessarily upward-monotone in current inclusion, the same union M works: every local witness is included in M, hence ΦM. If Φ is necessarily downward-monotone, use

    M[ā] := ∀R(ΦR → R[ā]).

M is included in every local witness, hence satisfies Φ. Monotonicity already entails extension-invariance. These principles are theorems of C, so neither is an omitted strengthening of B.

### 10.3 Universal relational Horn constraints

A more useful sufficient condition is that Φ(R) is a conjunction of universal Horn clauses in a relation variable R. In each clause R may occur as an atom in the antecedent, and the consequent is one R-atom or an R-independent formula; terms fed to R do not themselves depend on R. Other fixed parameters can occur throughout. If Φ has a solution at every world, take the pointwise intersection of all local solutions as above.

If the intersection satisfies a clause's antecedent at a world and tuple, then every solution satisfies its R-atoms, so every solution satisfies the consequent. For an R-consequent this puts the tuple in the intersection; for an R-independent consequent one existing solution proves it. Hence the intersection solves every clause. This gives a uniform solution in C. Finite tuples of relation unknowns are handled by coordinatewise intersection over all simultaneous solutions.

Totality clauses with existentially chosen outputs, or assertions of a unique selected member of an arbitrary nonempty set, are not covered by this Horn argument. They are exactly the sort of constraints capable of encoding the choice principles above.

### 10.4 A fixed finite menu

For a fixed list R₁,…,Rₙ, if □(ΦR₁∨…∨ΦRₙ), finite conditional pasting chooses the first successful candidate at each world. With extension-invariance this gives a uniform solution in C. This does not imply choice from arbitrary finite fibres: the pair-world and pair-individual countermodels have two-element fibres but no fixed finite list of global candidates covering every world.

## 11. The extensionality restriction is sharp against modal collapse

Even B+□Functional Choice does not validate unrestricted local-to-global witnessing

    □∃y φ(y) → ∃y□φ(y).

In a two-world full S5 model, let p be contingent and

    φ_p(y^t) := (p ∧ y=⊤) ∨ (¬p ∧ y=⊥).

At each world there is a witness, but one intensional proposition y cannot be identical to ⊤ at one world and ⊥ at the other. The model satisfies □Functional Choice, so this is a strict limit on its uniform-witness interpretation.

More generally, over B, even the special schema

    ∀p ∃y □[(p→y=⊤) ∧ (¬p→y=⊥)]

forces p→□p and ¬p→□¬p for every p. If p is true, the witness equals ⊤ here and hence necessarily, ruling out ¬p anywhere; the other case is symmetric. Thus every proposition has constant truth value. With B's world representation this is the one-world/extensional case, in which unrestricted witness exchange is trivial.

Therefore “extension-invariant” in §§5.1–5.2 must mean invariant under **current coextension**, not merely under necessary coextension. The latter is identity in the represented setting and imposes no useful restriction on Φ. This is a precise limitation on the uniform-witness characterization, not a proof of any absolute maximality of □Functional Choice among consistent principles.

## 12. Full external representation in the world direction still leaves object choice open

In §3 with |W|<κ, write B_{ᾱ} for the admitted rigid extensions at type ᾱt: exactly the supported subsets of D_{α₁}×…×D_{αₙ}. Then, as external sets,

    D_{ᾱt} ≅ (B_{ᾱ})^W.

This is the full external product, not merely an internally quantified family. A relation supplies its current extension A_w at each w. Since G fixes W, every A_w has the relation's support. Conversely, for an arbitrary external family (A_w) with A_w∈B_{ᾱ}, choose supports S_w, |S_w|<κ. Their union has size <κ. The relation whose value at ā is {w:ā∈A_w} is fixed by the corresponding common stabilizer and therefore belongs to D_{ᾱt}. Curried sections are admitted by the same support argument.

In particular, κ=ω₁, J=ω₁, W=ω has full external world-product representation at every original relational type, yet fails RC with target e. The missing functions concern choice across the large object domains; they are not missing world-indexed mixtures of admitted rigid extensions.

Under external ZFC, world-product fullness at every relation type implies IC: choose a witness a_w at each world, and paste the rigid singleton extensions {a_w}. The converse need not hold. An elementary countable Henkin substructure of a full infinite S5 structure preserves each internal IC/FC instance but cannot have a full external powerset of its countably infinite world set. To make this precise, include the world sort, evaluation relation, typed application, and logical/quantifier operations in a countable many-sorted language; singleton-world representation and separation of distinct propositions by worlds are first-order sentences inherited by elementarity. The resulting proposition domain is countable but its world set is countably infinite.

Thus “full world representation” has at least three distinct readings: internal representation, full external products of admitted rigid extensions, and full external powersets in the object direction. They should not be conflated.

## 13. Henkin Gallin expansions and genuine Infinity

The support construction has a direct Henkin expansion to Gallin-style extensional simple types. Introduce base sorts s=W, e=E, and o={0,1}; put all supported functions at every arrow type, including arrows ending in e or s. Use trivial action on o. Comprehension for the expanded language follows from exactly the equivariance proof in §2.

Translate original C types by

    e*=e,  t*=s→o,  (στ)*=σ*→τ*.

The translated domains agree with the original supported hierarchy. Evaluation at w is application of the translated proposition to w. Original equality gives a constant truth function on worlds, and □p is equality of p with the everywhere-true function. The expanded language includes extra typed operations, but its comprehension cannot escape the supported domains. These are **Henkin** Gallin models, not claims that every extensional function at every type is present.

For κ=ω₁, J=ω₁, W=ω, E=ω₁×{0,1}, every external map W→E is supported by the union of countably many singleton pair supports. Thus the Gallin individual-concept domain D_{se} is externally full. Section 12 proves analogous fullness for every world-indexed family of admitted rigid relation extensions. Nevertheless RC with target e fails by §3.3. Having a full domain of world-indexed individual concepts does not provide a choice function for arbitrary object-indexed families.

### 13.1 The axiom of Infinity, not only its finite-instance schema

In a full supported hierarchy the standard Frege numeral objects

    0, Suc(0), Suc²(0), …

are G-fixed, since zero and successor are pure equivariant constructions. Their external set N is therefore an admitted rigid property with empty support. It is inductive, so internal FiniteCardinality is contained in N. Conversely each standard numeral satisfies every admitted inductive property by ordinary external induction. Hence internal FiniteCardinality is exactly this standard sequence of numeral objects.

If D_σ is externally infinite, no standard finite cardinality holds of its universal property. Finite rigid subsets of D_σ are admitted, and the usual induction verifies that the nth numeral holds precisely of properties with n-element current extensions. Consequently the quantified Axiom of Infinity at σ holds, at every world. In particular the infinite pair-individual models satisfy □Axiom of Infinity at e, not merely the schema saying there are at least n individuals for each standard n.

This also shows that the countermodels use standard internal arithmetic, rather than relying on nonstandard Henkin natural numbers.

### 13.2 Type separation with infinite individuals on both sides

In §4 replace the singleton E by ω with trivial G-action. Intensional Choice at e still holds: for every necessarily inhabited F, select the least natural-number candidate at each world. The selecting relation has the support of F, because G acts trivially on the natural-number order. The pair-world failure of IC_t is unchanged. The strengthened model has infinite worlds and □Axiom of Infinity at e.

Together with §3 at κ=ω, J=W=ω, this proves independence of IC_e and IC_t over B even after adjoining □Axiom of Infinity at e. The §3 model has all e-free IC instances but fails IC_e; the modified §4 model has IC_e but fails IC_t.

## 14. Brief additional consequence: finite multiple selection

In either finite-support pair-flip model, every typed object has a finite G-orbit: a support of n pair indices has stabilizer of index at most 2ⁿ. This gives the following genuine weaker choice principles. Every serial relation has a subrelation whose fibres are nonempty and finite; every necessarily inhabited property has a subproperty whose extension is nonempty and finite at every world. The models still fail singleton selection as proved above.

For the relational assertion at a fixed world, take an allowed subgroup H supporting the relation and fixing that world. For each H-orbit of inputs choose a representative x and a permissible output y. Replace y by its finite orbit under H∩Stab(x); extend this finite output set equivariantly along the input orbit. Stabilizer invariance makes the extension well-defined. The resulting subrelation is H-supported, serial, and has finite nonempty fibres. For interworld selection, use worlds as the inputs and the same orbit construction, with an H supporting the given property. External AC chooses representatives for this model verification. Internal finiteness is actual finite extension by §13.1.

These principles should be coordinated with the separate choice/order research lane before being proposed as new records. No claim is made here about their equivalence to other familiar weak-choice principles in C or about their status under Maximalism.

## 15. Interworld Choice and complete-subalgebra retractions are independent

Write Ret for the proposed principle that every admitted internally complete Boolean subalgebra of the proposition algebra admits an internally complete Boolean-homomorphism retraction. The algebraic research lane identifies this, over B, with the existence of a transversal for every admitted rigid equivalence relation on world atoms. The following direct models independently establish its separation from IC.

### 15.1 All IC, but a complete subalgebra has no Boolean retraction

Let W=J×{0,1}, J infinite, with its pairing into P_j. This time use the **full wreath product** G=(Z/2Z)^J⋊Sym(J), all permutations preserving the pairing. Use finite point supports, which can always be closed under taking mates. Let E=ω with trivial action, to retain genuine individual Infinity. Construct the hierarchy as in §2. Then B and □Axiom of Infinity_e hold.

**All-type IC.** Suppose F⊆W×D_σ has finite mate-closed support S and is inhabited at every world. Choose u∉S and one candidate x∈F_u. Choose a finite mate-closed support A of x, and put T=(S∪A)\P_u. Since u∉S, T still contains S. For every w∉T choose a pairing-preserving permutation g fixing T and sending u to w, and put f(w)=gx. This is well-defined: any two such permutations differ by an element fixing T and u, hence also the mate of u, hence a support of x. It is equivariant under the pointwise stabilizer of T, and equivariance of F gives f(w)∈F_w.

For each of the finitely many w∈T choose a witness x_w∈F_w. Enlarge T to a finite mate-closed B containing supports of these witnesses. The completed f is equivariant under the stabilizer of B: its generic part was already equivariant under the larger stabilizer of T, and all exceptional inputs/outputs are now fixed. Thus its graph is admitted. This proves IC at every type. The argument uses only one generic witness and finitely many exceptional witnesses.

**The subalgebra.** Finite stabilizers have the fixed support points and a single infinite orbit outside their mate-closure, so D_t=FinCof(W). Let A consist of the propositions which are unions of whole pairs. It is an admitted rigid Boolean subalgebra. It is internally complete: a supported family of such propositions has a supported union/intersection, still a union of pairs. Every individual pair P_j belongs to A.

**No retraction, even without completeness.** Suppose an admitted Boolean-homomorphism retraction r:D_t→A exists, and let S be a finite support. Choose a pair P_j={a,b} disjoint from its mate-closure. Since r fixes A,

    P_j=r(P_j)=r({a})∨r({b}),
    r({a})∧r({b})=0.

Both r({a}) and r({b}) lie in A below P_j, so each is either 0 or P_j; exactly one must be P_j. The flip of this untouched pair fixes r and P_j, interchanges {a},{b}, and fixes both possible output values. Equivariance therefore gives r({a})=r({b}), contradiction.

Thus B+IC+□Infinity_e does not imply Ret. Equivalently the admitted partition into pairs has no supported transversal. This is not the earlier labeled-pair model: allowing permutations of pair indices destroys the problematic “choose from the next labeled pair” relation and makes the generic IC argument work, while the partition obstruction remains.

### 15.2 Ret does not imply IC

Use §3 with κ=ω, J=W=ω, worlds fixed by G, and pair-flipped individuals. The entire e-free hierarchy is full, including all predicates of propositions and all operators on propositions. Therefore an admitted internally complete Boolean subalgebra of P(W) is externally complete, corresponds to an ordinary partition of W, and admits a retraction by selecting one representative per block in external ZFC. The resulting operator belongs to the full D_tt. Thus Ret holds, whereas IC_e fails by §3.2. This model also has □Infinity_e.

Together these give independence of Ret and the full IC schema over B+□Infinity_e, by explicit ZFC Henkin models. Each is implied by full Relational/Functional Choice, but neither is forced by the other.

## 16. The all-type retraction schema recovers full Functional Choice

The scope of §15 matters. Let Ret_τ assert complete-homomorphism retractions for every admitted internally complete Boolean subalgebra of the Boolean algebra at relational type τ. Then **over B, the full schema Ret_τ is equivalent to Relational Choice, hence to □Functional Choice.** Proposition-only Ret_t is the genuinely weaker principle separated above.

The atom/partition duality used by the algebraic research lane works for every internally complete atomic Boolean algebra at a relational type, not only t: complete subalgebras correspond to admitted partitions of its atoms, and complete-homomorphism retractions correspond to admitted transversals of those partitions. Its proof uses internal joins, complete primality of atoms for admitted joins, and Plenitude to represent uniquely defined maps. The following supplies the nontrivial reduction from arbitrary typed choice to such partitions.

### 16.1 Typed atom coding

Fix a true proposition atom a, available by Actuality. For x^σ,y^ρ put

    δ_{a,x,y}[u,v] := a ∧ u=x ∧ v=y,

an object of relational type τ₀=σρt. This is an atom: any nonzero relation below it can hold only of the tuple (x,y), and the strong atom a decides that relation at the tuple; if it does hold anywhere under a, it holds everywhere under a. Rigid identities ensure the tuple restriction is stable. Two such atoms are equal iff their x and y coordinates are equal, since a is possible. This also follows directly from the world/tuple atom representation over B.

### 16.2 Ret_{σρt} supplies the (σ,ρ) choice instance

Let U^{σρt} be serial at the evaluation point. Rigid Comprehension gives a rigid U* coextensive there. Let S be the rigid property of τ₀-atoms coded by U*-pairs:

    S(b) iff ∃x,y(U*(x,y) ∧ b=δ_{a,x,y}).

On all τ₀-atoms define an equivalence relation E: two S-atoms are equivalent iff their x-coordinate agrees; every atom outside S forms its own singleton class. Coding injectivity verifies that this is an equivalence relation. Each x has a nonempty class by seriality. All parameters are fixed objects, identities/order tests are rigid, and U* is rigid, so E and S are admitted rigid relations.

Ret_{τ₀}, via typed atom duality, gives a transversal T. Define

    V(x,y) iff U*(x,y) ∧ T(δ_{a,x,y}).

There is exactly one selected coded atom in each x-class, so V is functional and included in U*. At the evaluation point it is therefore a functional subrelation of U. This works even when ρ=e; no operation with forbidden individual output has been used.

Thus the full Ret schema implies every Relational Choice instance. The reverse follows by choosing a representative atom from each internally coded partition class and reconstructing the complete retraction by inverse image along that choice. All required operations have relational output types and are represented by Plenitude.

**Why completeness matters:** a merely finitely additive Boolean homomorphism can behave as a nonprincipal ultrafilter on an infinite class, sending every singleton atom to zero while sending the class to its top. Complete preservation rules that out and forces an actual representative atom. Therefore do not silently weaken “complete homomorphism” in this equivalent formulation.

Suggested plain name: “Complete Retractions,” explicitly an all-relational-type schema. The definition audit now gives two mathematically different presentations of □Functional Choice over B: Uniform Extensional Choice (§5.2) and Complete Retractions at every relational type (this section).

### 16.3 Even proposition-only Ret plus all IC is insufficient

For completeness, the unordered nominal model G=Sym(W), finite supports, E=ω with trivial action satisfies both all-type IC and Ret_t, while RC at t fails on the family of unordered pairs of worlds. The IC proof is the generic-transport argument (one generic witness, finitely many exceptions).

To see Ret_t, consider an admitted rigid equivalence relation on worlds with finite support S. Outside S, full permutation symmetry makes the relation either equality or the universal relation. A class meeting both S and its complement must contain the entire complement. Hence the partition has finitely many exceptional classes, together with either one cofinite class or singleton classes outside S. Choose representatives of the finitely many exceptional classes and either one representative of the cofinite class or every outside singleton. The resulting transversal is finite or cofinite and admitted. Atom duality gives the complete retraction.

RC_t fails because no finite support can choose one of the two atoms of every unordered-pair proposition: swap an untouched pair. All models here retain □Axiom of Infinity_e. Thus the conjunction of the two weaker structural principles remains strictly below the all-type Complete Retractions / □Functional Choice schema.

## 17. Finite Boolean retractions do not recover complete retractions

This section supplies a direct ZFC-supported model, independent of any appeal to the literature on ordered permutation models. Let Q be the rational order, G=Aut(Q,<), E=Q, and let W be any fixed finite nonempty set with trivial G-action (two worlds give a genuinely modal example). Use the full finite-support hierarchy of §2. Then:

    B + □Infinity_e + IC_all + finite-Ret_all + ¬Relational Choice.

Here finite-Ret_all says: at each relational type, every admitted internally complete Boolean subalgebra has an admitted Boolean-homomorphism retraction preserving the finite Boolean operations. It does not demand preservation of arbitrary admitted joins/meets. The complete version fails, by §16. The proof is given below in enough detail to isolate every external choice and every internal closure claim.

### 17.1 Least finite supports for ordered atoms

For finite A,B⊆Q, write G_A for their pointwise stabilizers. The elementary group fact is

    G_{A∩B} = <G_A,G_B>.

To prove it, work separately in each open interval cut out by C=A∩B. Inside such an interval the remaining marked sets A\C and B\C are disjoint. The subgroup generated by the two stabilizers acts transitively on increasing tuples of any fixed finite length in that interval. Indeed any two such tuples can be connected by a finite sequence of single-coordinate moves preserving the order of the other coordinates. One construction first moves coordinates, from right to left, to an auxiliary tuple lying above both tuples, and then moves coordinates, from left to right, to their targets. Each coordinate travels in a gap between its fixed neighbors. Subdivide its journey at the finitely many A- and B-marks. A small move crossing an A-mark can be realized by an order automorphism fixing B and all other tuple coordinates; a small move crossing a B-mark can be realized by one fixing A and the other coordinates. Moves crossing neither are available in either stabilizer. Disjointness of the two marked sets ensures such neighborhoods exist. Homogeneity of the rational order extends each finite order-preserving partial map to an automorphism. This proves tuple transitivity.

Now, given g∈G_C, apply this transitivity to the increasing tuple of A\C in each C-interval. Obtain h in the generated subgroup agreeing with g on A. Then h^{-1}g fixes A, so g belongs to the generated subgroup, proving the group fact. This also covers points of A∩B, which remain fixed throughout.

Consequently, if finite A and B both support an object x at any type, A∩B supports it: both generators fix x. Starting with one finite support A, the intersection of all finite supports of x equals the intersection of finitely many subsets of A, so it too is a support. Denote this least support by supp(x). If gx=x, equivariance and minimality imply g(supp(x))=supp(x); an increasing permutation fixing a finite set setwise fixes it pointwise. Therefore

    Stab(x)=G_{supp(x)}.

This holds for arbitrary typed objects, including relation extensions and partition classes, not only finite tuples of individuals.

### 17.2 An invariant ultrafilter on a supported orbit

Fix a finite S⊆Q and H=G_S. Let O=H·x be any orbit of a supported object x. Write T=supp(x). An element of O is determined by moving the finitely many points T\S, in their fixed order, inside the open intervals cut out by S; points of T∩S remain fixed. Equality of these coordinate images implies equality of the transported object because an automorphism fixing T fixes x. Conversely least support makes this parametrization injective. Thus O is a finite product of spaces of increasing finite tuples in the S-intervals.

Let A⊆O be an admitted subset, with some finite support P. In each S-interval move all the coordinates of T\S to the right of every point of P in that interval, while preserving their prescribed order. Call the resulting nonempty set of configurations a P-tail. (An interval with no moving coordinates imposes no condition.) Its elements form one orbit under G_{S∪P}, so either the whole tail lies in A or the whole tail lies outside A. Enlarging P only shrinks to another nonempty tail; therefore this eventual truth value is independent of which finite support of A was used.

Declare A to belong to U_O exactly when its eventual truth value is true. The common tail obtained by taking the union of finitely many supports proves that U_O respects complements and finite intersections and contains O but not ∅. It is an ultrafilter on the Boolean algebra of admitted subsets of O. If h∈H, h carries P-tails to hP-tails, so U_O is H-invariant. This is a limiting choice along the rational order, not a selected element of O.

If O⊆C, push U_O forward to admitted subsets of C by A∈U_C iff A∩O∈U_O. The resulting ultrafilter is again H-invariant whenever H preserves C and O. Its characteristic predicate is admitted because this invariance gives it the finite support S. No assertion is made that U_O extends to all external subsets of O.

### 17.3 Uniform ultrafilters for the blocks of an admitted partition

Let an admitted partition of a supported typed set X have finite support S_0. Its class objects form an admitted set, and H_0=G_{S_0} acts on them. For each H_0-orbit of classes choose externally one representative C and one x∈C. This is ordinary metatheoretic ZFC choice, used to verify existence of a model object; it is not an internal Choice assumption.

The stabilizer of C inside H_0 is

    H_0∩Stab(C)=G_{S_0∪supp(C)}.

Apply §17.2 to the orbit of x under this subgroup, obtaining an ultrafilter U_C invariant under the full class stabilizer. Transport U_C along the H_0-orbit of C. This is well-defined precisely because of that stabilizer invariance: two transports to the same class differ by a stabilizer element. Do this for each externally chosen class orbit. The entire assignment C↦U_C is H_0-equivariant and therefore has the single finite support S_0.

This resolves the outer uniformity issue: merely finding an ultrafilter for each class would be insufficient. Here the orbit construction produces an admitted uniform family of them.

### 17.4 Constructing the finite Boolean retraction at every type

At relational type τ=α₁…αₙt, the ambient Boolean algebra consists of the admitted supported subsets of

    X=W×D_{α₁}×…×D_{αₙ}.

Let A be an admitted internally complete Boolean subalgebra, supported by finite S_0. For x∈X, the intersection of all members of A containing x is admitted (the family has support contained in S_0∪supp(x)), belongs to A by internal completeness, and is an atom of A. These atoms partition X. The atom assertion follows from complements: for every a∈A, the intersection is contained either in a or in its complement. They are admitted class objects, and their partition has support S_0.

Obtain the uniformly supported ultrafilter family (U_C) of §17.3. For each admitted ambient p⊆X, define r(p) to be the union of exactly those A-atoms C for which p∩C∈U_C. The selected family has finite support contained in S_0∪supp(p), so internal completeness puts r(p) in A. Uniform equivariance gives the whole map r the support S_0; hence r is an admitted object of type τ→τ.

Each U_C is an ultrafilter, so membership of the block C in r(p) respects 0,1, complements, and finite meets/joins. Thus r is a Boolean homomorphism. If p∈A, each block C is either included in p or disjoint from it; consequently r(p)=p. This proves the retraction property. Nothing in the argument depends on the arity or constituent types of τ.

### 17.5 IC, Infinity, and failure of Functional Choice

All IC instances hold because W is finite and fixed pointwise: choose a witness at each world and take the finite union of their finite supports together with that of the given property. The selecting graph is admitted. Infinity at e follows from §13.1 since Q is infinite.

Relational Choice fails already for individual inputs and outputs. The rational order gives the admitted rigid serial relation R(x,y) iff x<y. If a selector existed, fix one world and a finite support S of the selector. Choose x above every element of S. Its selected value y>x can be moved by an order automorphism fixing S∪{x}. That automorphism fixes the input, the chosen world, and the selector, contradicting uniqueness of the output. Hence RC_{e,e} and □Functional Choice fail. An alternative failure uses choosing a member from every nonempty open interval; the simpler strict-order relation already suffices.

Thus preserving only the finite Boolean operations is a genuine weakening even when imposed at every relational type, even with all interworld choice, individual Infinity, and more than one world. The complete retraction principle forces representatives; the finite retraction principle allows nonprincipal limiting ultrafilters.

## 18. The ordered model preserves all internally well-ordered joins

The model and retractions of §17 satisfy more than finite preservation. At every relational type, every admitted internally complete Boolean subalgebra admits a retraction preserving meets and joins of **every admitted family indexed by an internally well-ordered set**, at any index type. In particular it preserves every admitted sequence indexed by the internal natural numbers. Nevertheless RC_{e,e} fails.

### 18.1 Why well-ordered indices have a common pointwise support

Let I be an admitted index set with an admitted internal well-order L, and let P be a common finite support of I and L. For i∈I, its orbit O=G_P·i is P-supported and therefore is an admitted nonempty subset of I. Internal well-ordering gives an L-least member j of O. Every element of G_P preserves O and L, so it fixes the unique least member j. Since O is an orbit containing this fixed point, O={j}; in particular i=j. Thus G_P fixes every index in I.

This argument is essential: an internally well-founded order in a general Henkin model should not simply be treated as an externally well-founded order. Here the admitted-orbit argument proves exactly the pointwise fixation that is needed.

If f:I→B_τ is an admitted family and Q supports f, then P∪Q supports every value f(i), uniformly in i. For relationally represented functions the same conclusion follows from uniqueness of the output. No union of an infinite list of supports is required.

### 18.2 Common tails give preservation

Fix a block C of the subalgebra partition, and its invariant ultrafilter U_C constructed in §17. For a family (p_i) indexed by such an I, all p_i have the same finite support P∪Q. Relative to the finite support used to define the orbit inside C, there is a single common rightward tail on which the truth of every p_i is constant. If every p_i is U_C-large, the entire common tail lies in every p_i, hence lies in their intersection. Conversely, if the intersection is U_C-large, each p_i is large. Thus

    (⋂_{i∈I} p_i)∈U_C  iff  ∀i∈I (p_i∈U_C).

Blockwise, this says r(⋀_i p_i)=⋀_i r(p_i). Complements give the corresponding join identity. Empty families are included because the retractions preserve 0 and 1.

The statement concerns admitted families and admitted internal well-orders; it is not external closure under an arbitrary countable list of parameters or an arbitrary external ordinal-indexed family. For the natural-number instance, §13.1 identifies the internal naturals with the standard, G-fixed Frege numerals. Every admitted N-indexed sequence therefore has one uniform finite support, and the proof applies directly. An internally countably enumerable family also qualifies by its admitted enumeration, with repetitions harmless.

Hence replacing complete preservation by even “preservation of all internally well-ordered families” does not recover □Functional Choice. Under full Choice every admitted family can be well-ordered, but the separation model shows that using this reduction in the converse direction would be circular.

## 19. Infinity, Dedekind finiteness, and countable selection in the same model

These are additional calibrations of §17, not replacements for the fixed Infinity definition in the local framework. The model satisfies the quantified Frege Axiom of Infinity_e by §13.1, while its individual domain is internally Dedekind-finite.

### 19.1 Every admitted natural-number sequence of individuals has finite range

Represent a sequence by an admitted functional relation on the standard internal Frege numerals and individuals (or by a function in the Gallin expansion). If S supports the relation, then G_S fixes each numeral and therefore, by functionality, each selected individual. The only rationals fixed by G_S are the members of S. Thus the range is contained in S and is finite. In particular there is no admitted injection from the internal natural numbers into E.

### 19.2 Every admitted injective self-map of individuals is surjective

Fix a world and a functional graph for an injective self-map f:E→E with finite support S. For x∉S, the subgroup G_{S∪{x}} fixes f(x), so f(x)∈S∪{x}. On each open interval cut out by S, G_S acts transitively. If f(x) belonged to S at one point of that interval, equivariance would make f constant on the entire interval, contradicting injectivity. Therefore f(x)=x for every x∉S. For s∈S, equivariance gives f(s)∈S; the restriction to the finite set S is an injection and therefore a permutation. Hence f is surjective.

This argument is valid for the original relational graph formulation; it does not require adding the forbidden original arrow type e→e. In the Gallin expansion it is the usual function formulation.

### 19.3 Dependent Choice and a countably indexed selection instance fail

The admitted serial relation x<y has no admitted infinite chain indexed by the internal naturals, since every admitted individual sequence has finite range. Therefore the corresponding Dependent Choice instance fails.

There is also a direct countably indexed Relational Choice failure. For each internal natural number n, let the candidates be the admitted rigid n-element subsets of E. These are nonempty candidate classes, since finite subsets of Q are admitted. If an admitted selection n↦X_n existed with finite support S, every X_n would be fixed by G_S. A finite G_S-invariant subset of Q must lie inside S: every orbit outside S is an infinite open interval. Thus |X_n|≤|S| for all n, contradicting the candidate requirement at n>|S|. This uses a single uniformly defined relation indexed by the Frege naturals, not an arbitrary external sequence of unrelated parameters.

The combined calibration is consequently strong: B, quantified individual Infinity, all IC, and all-type retractions preserving every internally well-ordered family coexist with failure of Dependent Choice and this explicitly countably indexed choice instance. This does not conflict with the retraction preservation theorem: a nonprincipal ultrafilter can be countably complete relative to admitted sequences when the underlying infinite domain has no admitted countable enumeration.

## 20. The exact type-local content of Extensional Witnessing

Section 5 proves a full-schema equivalence LG≡IC, with a type shift in one direction. Over B there is a more precise type-local formulation:

    LG_τ  iff  IC restricted to rigid candidates of relational type τ.

Here restricted IC means that every necessarily inhabited property F of rigid τ-objects has a necessarily unique selecting subproperty. This quantifies over a genuine subdomain of admitted τ-objects; it does not mean merely requiring that the selecting graph be rigid.

Over B every current τ-extension has a unique rigid representative. Existence is Rigid Comprehension; uniqueness follows because coextensive rigid relations are necessarily coextensive (using BF) and C's Intensionality identifies them. These are the same rigid-core facts established in the world-representation report.

For restricted IC⇒LG, rigidify a local Φ-witness at each world in the local argument. Extension-invariance preserves Φ, so necessarily there is a rigid Φ-witness. Restricted IC selects such witnesses, and the ordinary existential mixing formula from §5 produces one global relation with the selected current extensions.

For LG⇒restricted IC, given a necessarily inhabited F of rigid candidates define

    Φ_F(M) := ∃R(Rigid(R) ∧ F(R) ∧ R≈τM).

This is extension-invariant in M and necessarily inhabited. LG gives one M with □Φ_F(M). The property

    G(R) := Rigid(R) ∧ F(R) ∧ R≈τM

is necessarily inhabited and necessarily unique, by uniqueness of the rigid representative, and lies below F. It is the required selector. The proof is syntactic over B and does not assume external fullness.

At τ=t the rigid candidate domain has only ⊥ and ⊤, explaining why LG_t is already a theorem of C. At τ=σt, rigid singleton predicates encode arbitrary σ-objects, explaining why LG_{σt} implies IC_σ. It need not follow from IC_σ.

### 20.1 A strict separation already at individual properties

Modify §17 by taking W=ω, fixed pointwise by G, instead of finitely many worlds. Keep E=Q, G=Aut(Q,<), and finite supports. All the support, retraction, and well-ordered-family-preservation arguments of §§17–18 remain valid: they did not require W to be finite. Both quantified Infinity_e and Infinity_t hold. The following sharper type profile holds:

* IC_e holds.
* Every e-free IC instance holds, including IC_t.
* LG_et fails, so IC at the higher rigid-property domain fails and the full IC schema fails.

For IC_e, let S support a necessarily inhabited F. Every current fibre F_w⊆Q is G_S-invariant. There are only finitely many G_S-orbits on Q: the singleton support points and the open intervals cut out by S. Choose one representative of each of these finitely many orbits. Every nonempty fibre contains one member of this fixed finite menu; choose its first eligible member. The selecting graph is supported by S together with the finite menu, independently of how many worlds there are.

The e-free hierarchy is externally full and has trivial G-action because W is fixed and no individual sort occurs. External ZFC choice therefore supplies every e-free interworld selector, and its graph has empty support. The same finite-orbit argument as for e gives selection of any fixed finite tuple of individuals, since G_S has finitely many orbits on Q^k for each fixed k.

For failure of LG_et, label the fixed worlds w_n by n∈ω. Let Φ(R) at w_n say that the current extension of the individual property R has exactly n members. This is an admitted, empty-supported predicate of R: order automorphisms preserve finite cardinalities. It is extension-invariant and has a local witness at every world, since every finite subset of Q is admitted. If a global M satisfied Φ at every world, take a finite support S of M. Each finite slice M_{w_n} is G_S-invariant, hence is contained in S. Therefore n=|M_{w_n}|≤|S| at every n, contradiction.

This is a single admitted extensional witness problem with unbounded finite requirements. It shows that IC_e together with all e-free IC, even supplemented by all-type well-ordered-family-preserving retractions and Infinity, does not supply the next-level extensional witnessing principle. The full-schema/type-local distinction in the proposed definition is mathematically substantial.

## 21. General world sets and a separation from finite multiple selection

### 21.1 The retraction theorem does not require fixed finite worlds

The retraction conclusions of §§17–18 hold with **any** G=Aut(Q,<)-set W whose elements have finite rational supports. Their proofs use only that each ambient atom carrier X=W×D_{α₁}×…×D_{αₙ} is a supported G-set. Least supports, orbit coordinates, invariant ultrafilters, and uniform class-orbit transport then apply exactly as written. Fixed finite W was used solely to establish IC_all in §17.5.

In particular the ordered-endpoint world construction in the algebraic report (worlds are the nonconstant finitely supported subsets of Q) inherits all-type retractions preserving every internally well-ordered family. That model has separately an extension-universal relation and a world-separating relation, but no relation with both properties. Its additional retraction principles do not supply the missing common exact witness. No IC claim is made for that construction; indeed IC_e fails by requiring an individual above every essential endpoint of the current nonconstant world, then placing those endpoints above any proposed selector's support.

All of these ordered support models also admit the common-finite-parameter infinitary extensions of §7.1, by the same equivariance proof. They are not closed under arbitrary infinitary formulas with unbounded independently supported parameters.

### 21.2 Finite retractions and finite multiple selection are independent

Finite multiple selection asks for a subrelation with a nonempty finite output fibre for every input, instead of a singleton fibre. It is not equivalent to allowing a finitely additive Boolean retraction.

In the ordered model of §17, finite multiple selection already fails for the serial relation x<y. Suppose a proposed selecting subrelation has finite support S. Choose x above S. Its finite nonempty output fibre would be invariant under G_{S∪{x}}. Any finite invariant subset of Q is contained in the fixed points S∪{x}, but none of these is greater than x. This is a contradiction. Thus all-type finite retractions, even preserving all internally well-ordered families and accompanied by IC_all, do not imply finite multiple selection.

Conversely, the finite-support independent pair-flip model of §14 satisfies finite multiple selection at all types by finite stabilizer-orbit averaging. It has no finite Boolean retraction for the admitted complete subalgebra determined by the pair partition of the individual atoms (embedded at a relational type using a fixed world atom). On a two-element block a Boolean ultrafilter is principal, so a retraction would select one member of each pair. Flipping a fresh unsupported pair gives the usual contradiction. Hence finite multiple selection does not imply all-type finite retractions.

These comparisons concern explicit Henkin higher-order schemas. No identification with a named set-theoretic weak-choice axiom, or novelty claim, is intended.

## 22. Functional Choice factors into finite multiple selection and finite retractions

Let MC be the all-type schema saying that every serial relation has a subrelation with nonempty internally finite fibres. “Finite” means the existing Frege finite-cardinality notion, not external standard finiteness. Let finite-Ret be the all-relational-type finite Boolean retraction schema of §17. Then, over B,

    MC + finite-Ret  ⇔  Relational Choice  ⇔  □Functional Choice.

The forward reduction is concrete. Apply MC to a serial relation U to obtain a subrelation V with nonempty finite rows. Encode its fibres as blocks of relational atoms using §16.1; all remaining atoms form singleton blocks. The resulting admitted partition has internally finite nonempty blocks. A finite Boolean retraction for its complete subalgebra gives, on each block, an admitted ultrafilter. Such an ultrafilter is principal when its block is internally finite. Its unique principal point is definable from the retraction, so the selected points assemble into one admitted relation. Decode the selected atom in each row to obtain a functional subrelation of V and hence U.

The principality assertion does not assume externally standard natural numbers. It is proved by the internal Frege induction already available in the framework. The empty-block case admits no proper ultrafilter. At a successor-sized block choose one point a for the local argument. If {a} belongs to the ultrafilter it is principal there. Otherwise the complement of {a} belongs to it; restriction gives an ultrafilter on the smaller block, and induction supplies its principal point. The induction predicate quantifies over all blocks and all admitted ultrafilters, so the resulting theorem applies to every internally finite block. No uniform choice of the auxiliary a is used in this local proof.

Conversely, Relational Choice gives MC by singleton selection and gives complete retractions by §16, hence finite retractions. The two factors are independent by §21.2: the pair-flip hierarchy has MC but lacks finite-Ret, whereas the ordered hierarchy has finite-Ret (indeed well-ordered-family preservation) but lacks MC. Both can have individual Infinity, and the ordered countermodel can additionally have all IC.

One can weaken the retraction factor to the restriction to partitions with internally finite blocks. That restriction is precisely finite-fibre Relational Choice, by the same coding and principality argument. The all-type finite-Ret formulation is structurally broader, but its conjunction with MC yields exactly the same full Functional Choice principle. This is an equivalent factorization under the stated base, not a proposed revision of the original definitions.

## 23. Uniform Extensional Choice as typed choice over worlds and inputs

There is an equally precise type-local reading of §5.2. Over B, US_{σ,τ} is equivalent to the following restricted rigid choice principle:

> Every admitted rigid serial relation from pairs (a,x), where a is a proposition atom and x has type σ, to rigid τ-objects has an admitted rigid functional subrelation on those rows.

Thus its indices are worlds together with ordinary inputs, and its outputs are rigid extensions of the requested relational type. “Pairs” are polyadic arguments or their standard haecceity codes, not a new primitive product type. This is an internal typed equivalence, not external full-function-space choice.

For restricted choice⇒US, given Φ(x,M), rigidify each local candidate extension. Encode eligibility by

    U(a,x,R) := Atom(a) ∧ Rigid(R) ∧ □(a→Φ(x,R)).

The premise of US, strong atom decision, and BF give a nonempty row for every atom a and input x, just as in §5.3. Choose a rigid unique S(a,x,R) below U and define

    F[x,ā] := ∃a,R(Atom(a) ∧ a ∧ S(a,x,R) ∧ R[ā]).

At each world its unique true atom identifies the selected rigid R. Fx is coextensive with that R, so extension-invariance gives Φ(x,Fx). This is the required F.

Conversely, given a rigid serial U on these rows, put

    Φ(x,M) := ∃a,R(Atom(a) ∧ a ∧ Rigid(R) ∧ U(a,x,R) ∧ R≈τM).

This is necessarily inhabited and extension-invariant in M. Apply US to obtain F. Define the selected rigid relation by

    S(a,x,R) := Atom(a) ∧ Rigid(R) ∧ U(a,x,R)
                ∧ □(a→R≈τFx).

Existence follows by applying the strong-atom/BF argument to the witnesses supplied at the a-world; uniqueness follows from uniqueness of the rigid representative of a current extension. All conjuncts are rigid, so S is a rigid selector. This proves the converse.

At τ=t, US_{σ,t} is already a C theorem for every σ: use F(x):=Φ(x,⊤), with the same two-truth-value argument as for LG_t. This guards against proposing a vacuous propositional-output fragment as a new principle. At τ=ρt, singleton rigid predicates encode arbitrary ρ-objects; the full US schema therefore recovers all typed choice, as §5.2 proved.

## 24. Why ordinary finite-support models cannot separate EU_e + IC_e from individual-output choice

The implication

    B + EU_e + IC_e  ⇒  RC with arbitrary inputs and output e

is **not proved here**, and no countermodel is claimed. A broad obstruction eliminates the most immediate permutation-model constructions.

Suppose E is an infinite atom set with a group G of permutations, the hierarchy consists of all finitely supported functions, and:

1. Every admitted world w has a least finite E-support supp(w), equivariantly under G.
2. For every finite A⊆E, every orbit of the pointwise stabilizer G_A on E\A is infinite.

Then **EU_e implies failure of IC_e**, regardless of the chosen supported world set W.

To prove this, let R witness EU_e and choose a finite support S of R. Define a world-indexed eligible set by

    F(w,x)  iff  x∉S∪supp(w).

Least support is equivariant, so F is supported by S and therefore is an admitted predicate. Every row is nonempty because E is infinite and the excluded set is finite. Suppose an IC_e selector exists and has finite support T; enlarge T to contain S. By EU_e some world w has R-slice exactly T, since the rigid property T is admitted. The finite set S∪supp(w) supports this slice. Any finite support A of the finite set T must contain T: if t∈T\A, the infinite G_A-orbit of t would lie in the invariant finite set T. Consequently

    T⊆S∪supp(w).

The group H=G_{S∪supp(w)} fixes both w and the proposed selector. It must therefore fix the unique selected individual. But that individual lies outside S∪supp(w), where every H-orbit is infinite. Contradiction.

The hypotheses hold for the ordinary unordered-atom and ordered-rational-atom hierarchies used above. The theorem explains why enlarging their world sets to cover every admitted individual extension destroys IC_e. It does not establish the displayed implication for arbitrary Henkin models: least finite supports, external fullness among supported functions, and the orbit hypothesis are extra semantic assumptions.

There is also a corresponding direct obstruction for the independent pair-flip hierarchy. Use least finite pair-index supports, and let F(w,x) require the pair containing x to lie outside S∪supp(w). Given a proposed selector support T⊇S, choose a finite individual property containing exactly one atom from each pair indexed by T. Every pair-index support of this property contains T. A world realizing that property therefore allows a fresh pair flip fixing the world and selector but moving the selected individual. Hence the standard pair-flip models cannot provide the missing separation either.

### 24.1 Unordered small supports: no least-support assumption is needed

There is a stronger theorem for G=Sym(E). Let κ be any infinite cardinal with κ≤|E|, and admit all objects/functions supported by sets of fewer than κ individual atoms. Every world must have such a support. No regularity of κ and no least-support property of worlds is required. Then again

    EU_e ⇒ ¬IC_e.

Let S support the proposed universal relation R. For each world w put H_w=Stab(w)∩G_S. Choose any small support A of w containing S. Since G_A≤H_w, the complement E\A lies in one H_w-orbit, which has cardinality |E|. Every other orbit lies inside A and has cardinality less than κ. Hence H_w has a unique orbit O_w of cardinality at least κ, independently of the chosen A. The family F(w,x) iff x∈O_w is G_S-invariant, admitted, and inhabited at every world.

Suppose a selector for F has small support T⊇S. Choose by EU a world w whose R-profile is T. Then H_w preserves T setwise. For any small support A of w containing S, invariance of T under G_A implies T⊆A: otherwise its orbit E\A, of size at least κ, would be contained in T.

Let x be the selected point of O_w. Choose g∈H_w with gx outside A, and a transposition k of gx with another point outside A. Thus k∈G_A≤H_w. The conjugate g⁻¹kg belongs to H_w, moves x, and fixes T pointwise: g maps T into T⊆A, where k is the identity. It therefore fixes w and the selector while moving its unique selected value, contradiction.

This covers finite-support and countable-support unordered-atom hierarchies, including supported worlds with no least support. It still depends on the full symmetric group and on admitting all supported predicates, so it is not a theorem about arbitrary Henkin models. The cardinal language in the construction is external ZFC used to define an equivariant predicate; no internal cardinal-comparison assumption has been inserted.

### 24.2 Small-support independent pair flips

The pair-flip obstruction also extends without least supports. Let E=J×{0,1}, let G be all independent flips of the pairs, and allow supports of fewer than κ pair indices, where κ≤|J| is infinite. Let S support R and put H_w=Stab(w)∩Fix(S). Define F(w,x) to mean that some member of H_w moves x. This is an admitted S-supported family. Each row is nonempty: a small support A of w containing S leaves a fresh pair, whose flip belongs to H_w.

If a selector has small support T⊇S, choose one atom from each pair indexed by T and let X_T be the resulting admitted individual property. An EU world w realizes X_T. Every member of H_w preserves X_T, and independent pair flips cannot permute the indices. Hence it fixes every pair indexed by T pointwise; that is, H_w≤Fix(T). Thus H_w fixes the selector and w, while the selected value is required to be moved by some member of H_w. Contradiction.

In particular neither the finite-support nor the countable-support independent-pair hierarchy can settle the unresolved EU_e+IC_e boundary by changing only its supported world set.

## 25. A projective-set transfer and the precise unresolved boundary

This section gives a mathematical reduction, not a claimed consistency result. Work internally in any classical set universe M satisfying ZF. A set W is projective if every surjection onto W has a section. Equivalently, every W-indexed family of nonempty sets has a choice function. The equivalence follows by taking the disjoint union of a family in one direction and the fibres of a surjection in the other; these constructions use only ZF.

Fix a nonempty individual set E∈M. Suppose there is a surjection

    π:W→P^M(E)

with W projective in M. Form the constant-domain full-in-M S5 hierarchy with worlds W, individuals E, propositions P^M(W), and all function spaces computed in M. This is a Henkin model when viewed externally if M omits external subsets or functions. More formally, for arbitrary possibly nonstandard M, use its internally coded hierarchy and application relation; truth of each standard formula is verified by the usual external induction on that formula.

The resulting hierarchy satisfies:

    C + □Plenitude + EU_e + IC_all.

Comprehension and C follow because the denotation of every standard formula, with its finitely many parameters, is a set/function of M by Separation and Replacement. Singleton world-tuple atoms belong to M, so every nonempty relation contains an admitted atom. Identity is the equality of M-objects. Extensionality of the underlying set-functions gives relational Intensionality, and identity/inequality are world-independent, giving necessitated Distinctness; no current-coextension Extensionality principle is asserted. Directly, a locally functional relation can be frozen at its world by Separation; unique values give its rigid graph without any appeal to Choice, proving □Plenitude as in §1.

For EU_e, define R(w,x) iff x∈π(w). Every rigid individual property is a member of P^M(E), so surjectivity of π gives a realizing world. For IC at any type σ, an admitted modal predicate F gives a W-indexed family of nonempty subsets of D_σ. Projectivity of W supplies a function g∈M choosing from this family. Its singleton graph w↦{g(w)} belongs to the typed hierarchy and is the required IC selector. Thus even all IC, not just IC_e, hold.

Now suppose the displayed implication of §24 were a theorem valid in all such Henkin models. It would give a choice function for the family of all nonempty M-subsets of E: use the input type et for rigid individual properties, with eligibility X(x); give non-rigid or empty inputs a fixed default individual to make the whole relation serial. Restrict the resulting selector to rigid nonempty properties. A choice function on P^M(E)\{∅} well-orders E by the ordinary ZF argument using Hartogs' ordinal and transfinite recursion. This proves the following conditional consequence entirely within ordinary set theory:

> If B+EU_e+IC_e implies individual-output Relational Choice in general, then ZF plus the Presentation Axiom implies the Axiom of Choice.

Here the Presentation Axiom says that every set is a surjective image of a projective set. Apply it to P(E), and apply the argument separately to every nonempty E. Conversely, a model of ZF plus the Presentation Axiom plus failure of AC would immediately supply a counterexample to the modal implication, after choosing a non-well-orderable E. **No such classical set-theoretic model is asserted here.**

For terminology and historical context, Aczel's 1978 chapter, §7, printed p.65, defines a base as a set on which choice functions can always be found and a presentation as a surjection from a base: [primary chapter scan](https://www.cs.cornell.edu/courses/cs6180/2017fa/notes/week4/lecture8/Aczel_type-theory-set-theory.pdf). Andreas Blass's [author answer dated 23 October 2010](https://mathoverflow.net/questions/43323/existence-of-enough-projectives-in-the-category-of-sets) reports no then-new information about whether enough projective sets imply Choice in classical ZF and identifies the same axiom as Aczel's Presentation Axiom. This is verified historical evidence only; the present report does **not** claim that its current literature status was exhaustively checked. The transfer argument above is independent of that historical-status statement.

The available positive results require a genuine descent mechanism. EU_e plus a complete retraction for the Boolean algebra of its equal-profile classes gives a section of π; pulling a world selector back along that section yields individual-output Choice. A single relation whose profiles are both universal and separating gives the section immediately. EU_e alone supplies no such section, and taking an arbitrary selector on the covering worlds does not make its values constant on equal-profile fibres.

## 26. Well-ordered Boolean preservation selects every well-order-separated output field

This is a further consequence of the stronger retractions in §18. It is an original argument in this report, not a literature-novelty claim. Work over B. Say that a rigid field Y of type ρ is **separated by a well-ordered family** if there are a rigid index field I of some type, an admitted internal well-order of I, and an admitted rigid relation C(i,y), such that

    forall y,z in Y [ (forall i in I (C(i,y) iff C(i,z))) -> y=z ].

The word “well-ordered” has its internal higher-order meaning. The displayed data are a single admitted family, not an external list of predicates. Equivalently, the map y ↦ {i in I : C(i,y)} is an admitted injection from Y into the represented powerset of a well-ordered field. This is a definition of the needed coding condition; no change to the original C type language is required, because graphs represent any unavailable function type.

**Theorem.** The all-type retraction schema preserving every admitted internally well-ordered family implies Relational Choice for arbitrary input types whenever the output field Y has such a separating family.

**Proof.** Let U(x,y) be a serial relation with y constrained to Y. Use the atom coding in §16 to make its rows into blocks B_x of an admitted partition (at each relevant world atom); add singleton blocks for all unused atoms. The retraction gives a uniformly represented ultrafilter K_x on each nonempty row. Fix x locally. For i in I, put

    A_i = { y in U_x : C(i,y) iff {z in U_x : C(i,z)} belongs to K_x }.

Boolean ultrafilter laws give A_i in K_x for every i. The family i ↦ A_i is admitted, with the fixed internal well-order on I. Preservation of its meet gives the intersection A = intersection_i A_i in K_x, so A is nonempty. All members of A have the same C-coordinates, hence the separating condition makes A a singleton. Its unique member is definable from U, C, and the retraction; therefore the choices assemble uniformly into one admitted functional subrelation. Empty I causes no difficulty: separation then already says that Y has at most one member. The world-tagged construction selects uniformly at all relevant world atoms, and rigidification/freezing over B gives the usual equivalent RC/functional-choice formulation. No well-order of the input field or of Y was assumed. ∎

Consequently, over B,

    well-ordered-family retractions at all types
    + every typed field is separated by an admitted well-ordered family
    iff □Functional Choice.

For the reverse direction, full choice well-orders each field, so its singleton predicates supply the separating family, and §16 gives complete retractions. This is another exact factorization, with the coding condition stated explicitly; no identification with a named set-theoretic weak-choice axiom is required for the theorem.

A useful special case concerns represented reals: subsets of an internally well-ordered natural-number field are separated by their membership coordinates. Hence the retractions of the ordered-atom model give choice from arbitrary admitted families of nonempty sets of such represented reals, even though choice on individuals fails already for x<y. There is no contradiction with §19's failure of countable selection of finite individual sets: those candidate outputs are subsets of the ordered atom field, which has no admitted well-ordered separating family.

**How much stronger is the separating-family condition than well-orderability?** By itself it is weaker: represented subsets of a well-ordered field have the membership-coordinate family, whether or not their powerset is internally well-orderable. The conditional full-in-a-choiceless-ZF construction makes this distinction literal whenever that powerset is not well-orderable. Under the well-ordered-preserving retraction hypothesis, however, the theorem makes the two conditions equivalent for a fixed Y. Apply it to the membership relation between nonempty subfields of Y and their members. Its selector well-orders Y by the internal Zermelo argument: take all admitted well-ordered partial choice-recursion chains, ordered by initial-segment inclusion, and form their union by comprehension. They are comparable because a first disagreement would violate the unique chosen next value. Every admitted nonempty subset of the union has a least member by meeting one chain containing one of its members; hence the union is internally well-ordered. If it omitted any member of Y, the selector on the complement would extend it, contradicting its construction as the union of all chains. Thus the distinction concerns the coding hypothesis before retraction preservation is added, and the theorem explains exactly why adding preservation closes it.

## 27. A precise diagonal obstruction for projective world covers

The following conditional calculation isolates an extra assumption that would settle the individual-output issue positively. It does not show that EU supplies this assumption. Work over B, identify worlds with proposition atoms, and represent individual-valued maps by their rigid functional graphs. Suppose there are an admitted internally well-ordered field A and an admitted surjection

    g : A × W -> {all admitted rigid functional graphs W -> E}.

Assume IC_e. For each w put E_w={g(a,w)(w):a in A}. Each E_w is internally well-orderable, by ordering its members using their least preimages in A. If every E_w were a proper subfield of E, world-indexed individual choice would give an admitted function f with f(w) outside E_w for every w. Surjectivity supplies a0,w0 with g(a0,w0)=f. Then f(w0)=g(a0,w0)(w0) belongs to E_w0, a contradiction. Hence E=E_w for some w, so E is internally well-orderable and arbitrary-input individual-output choice follows by taking least eligible elements.

All displayed function spaces mean represented fields of graphs and all displayed maps may be expressed relationally. Least preimages, diagonal evaluation, and the field w↦E_w are admitted by comprehension. The argument does not assume that an internal well-order is externally well-founded.

This is the familiar diagonal shape of the obstruction to combining a projective cover with a single bounded source of choice failure. Here its exact modal use is conditional on the displayed cover. EU_e gives W→P_int(E), which is a different cover; no construction of g from EU_e is available in these notes. Consequently this observation strengthens the explanation of failed model attempts without upgrading the unresolved EU_e+IC_e implication to a theorem.

## 28. Universal profiles plus interworld choice transfer proposition retractions to individual ultrafilters

Work over B. Suppose R:et witnesses EU_e, finite Boolean Ret_t holds, and IC_e holds. Then there is a uniformly admitted assignment of an ultrafilter concentrated on each nonempty rigid individual field X. Consequently every admitted serial relation, with arbitrary input type and individual outputs, has a uniformly represented row-ultrafilter assignment. This is individual-output ultrafilter-valued choice; it is not a claim of ordinary Relational Choice.

For each rigid X define its profile proposition

    b_X := forall x (Rx iff Xx).

EU makes b_X nonzero. Distinct rigid X give disjoint blocks, and every world lies in some b_X by rigid comprehension. These blocks therefore form the atoms of the admitted internally complete Boolean subalgebra of profile-saturated propositions. Let r be a finite Boolean retraction onto that subalgebra. For a proposition p, the condition

    U_X(p) iff b_X <= r(p)

defines an ultrafilter on world propositions concentrated on b_X. This follows because b_X is a nonzero atom of the target subalgebra, r preserves finite Boolean operations, and r(b_X)=b_X.

Apply IC_e to the everywhere inhabited relation

    F(x) := ((exists y Ry) -> Rx).

Obtain an admitted M:et which has exactly one individual in its extension at every world and whose value belongs to the R-profile whenever that profile is nonempty. Define, for rigid individual fields Y,

    beta(Y) := exists x (Mx and Yx),
    K_X(Y) iff b_X <= r(beta(Y)).

The unique-value property of M makes beta a Boolean homomorphism. Thus K_X is a proper ultrafilter. If X is nonempty, every world in b_X has its M-value in X; hence b_X<=beta(X), and monotonicity of r gives K_X(X). All definitions use the fixed parameters R,r,M, so the family X↦K_X is uniform. For an arbitrary current serial relation U(a,x), rigidly freeze its current extension and apply the assignment to its nonempty rows. This gives the asserted arbitrary-input individual-output row-ultrafilter choice.

The preservation strength transfers exactly. If r preserves meets of every admitted internally well-ordered family, so does each K_X. For such a family (Y_i), the unique-value property gives

    beta(intersection_i Y_i) = meet_i beta(Y_i),

as a proposition identity; retraction preservation and evaluation at the target atom b_X then give the corresponding meet law for K_X. The same argument works for represented countable families when that is the preservation assumption. These are internal admitted families, not arbitrary external lists.

Combining this with the signed-coordinate argument of §26 yields the useful sufficient condition

    EU_e + IC_e + well-ordered-family Ret_t
    + a well-ordered separating predicate family on E
    => arbitrary-input Relational Choice with individual outputs.

For a represented countable separating family, countable-family Ret_t suffices. With complete Ret_t, all subsets/singletons may be used, recovering the earlier EU_e+IC_e+complete-Ret_t bridge without a separate coding assumption. None of these reductions removes its retraction hypothesis, and the bare EU_e+IC_e question remains unresolved.

## 29. The small-support obstruction extends to arbitrary independent transitive blocks

The pair-flip obstruction in §24.2 has a useful broader form. Let E be the disjoint union of nonempty blocks E_j, j in J, with |E_j|≥2. Let G_j act transitively on E_j and trivially on the other blocks, and let G be their direct product (the same argument works for the direct sum). Use coordinate supports of size <κ, where κ is infinite and |J|≥κ. Let W be any G-set whose elements have such supports, and take the full supported hierarchy of §2. Then

    EU_e implies failure of IC_e.

There is no assumption that worlds have least supports. For a world w define

    B_w := { j in J : some g in G_j satisfies g w != w }.

If A supports w, then B_w⊆A, so B_w is small. Each component G_j is normal in G, hence B_{g w}=B_w for every g. If R witnesses EU and has coordinate support S, the relation

    F(w,x) iff x belongs to a block E_j with j outside S union B_w

is admitted: it is equivariant, with S a permitted parameter support, and is inhabited at every w because S∪B_w is small. Here the meta-index j need not be a separate object-language sort; equivariance of this external relation is exactly what admits it to the full supported hierarchy.

Suppose an admitted world-indexed individual selector f existed, and enlarge its small support T to contain S. Choose, in the ZFC metatheory, a point a_j in each block j∈T. The field X={a_j:j∈T} is T-supported, so EU supplies a world w whose R-profile is X. For j∈T\S, if j were outside B_w, every element of G_j would fix w and R, and would therefore preserve X. Transitivity and |E_j|≥2 contradict preservation of the singleton X∩E_j. Thus T\S⊆B_w.

The chosen f(w) belongs to some E_j with j outside S∪B_w, hence outside T. By definition of B_w every element of G_j fixes w; because j is outside T it also fixes f. Transitivity supplies an element of G_j moving f(w), contradicting equivariance of evaluation. This refutes IC_e.

Only finite unions of small supports were used, so κ need not be regular. The argument includes finite permutation blocks of every size, not merely pairs, and also includes infinite transitive component actions. It concerns the full supported hierarchy: a narrower Henkin domain might omit F, so no claim is made for arbitrary sparse Henkin models with the same underlying action.

## 30. Compact truth spaces can supply all interworld choice without supported worlds

The world-representation research lane constructed the following separate model to test weaker evaluator principles. Let W=G=2^N with translation action, let G_S be the subgroup fixing the finitely many coordinates in S, and admit exactly the G_S-supported objects. Take fixed individuals E=N. Then D_t consists of the finite-coordinate clopen subsets of Cantor space, and higher domains consist of all finitely supported functions between the preceding domains.

This construction satisfies C and constant-domain □ND/BF, but its semantic world points are not supported objects. Formula and lambda closure still follow from equivariance: a truth set invariant under G_S is a union of the finitely many G_S-cosets and is therefore admitted. Singleton predicates on admitted typed objects are supported by the object's support, so object identity is genuine. Proposition atomicity fails because every nonempty cylinder splits on a fresh coordinate. Thus the unsupported-world feature prevents application of §2.2–2.3; it does not prevent C-soundness.

**All-type IC strengthening.** If F:σt is everywhere inhabited, its clopen truth sets {Fx:x in D_σ} cover Cantor space. External compactness supplies a finite subcover Fx_1,...,Fx_n. Give the candidates this finite priority order and choose x_i exactly where F x_i first holds. The resulting selector is admitted by comprehension with these finitely many parameters and satisfies IC_σ. This applies to every type. The metatheory is ordinary ZFC, as in the other explicit models; the argument makes no internal well-order or unrestricted choice assertion.

There is nevertheless no supported bivalent complement-preserving evaluator E:tt. If S supports E, choose a coordinate n outside S and flip just that bit. The flip fixes E, top and bottom, and interchanges the coordinate cylinder p_n with its complement. Bivalence makes E(p_n) fixed by the flip, so equivariance forces E(not p_n)=E(p_n), contradicting complement preservation. In particular finite Boolean evaluator density and even a finite Boolean retraction onto {bottom,top} fail.

Consequently this model has C5, all IC, and quantified individual Infinity, while lacking proposition atomicity and these weak Boolean evaluator principles. A useful scope check is that the equivariant pair family {p_n,not p_n} does not refute ordinary relational choice: the relation selecting whichever candidate is currently true is necessarily functional. A finite-support bit-flip argument refutes an operation or rigid selector for that family, because its object output must be fixed; it cannot treat the semantic Cantor world as fixed by the bit flip. Full details of its evaluator role belong to `research/2026-10-22/evaluation-and-choice/structural-world-representation.md`; the compactness proof of all IC was supplied and audited in the collaboration between these lanes. There is no novelty claim.

It is essential not to call this a full world-sort Gallin expansion with the same proposition domain. If every actual Cantor point were a world object and equality/comprehension applied to it, the formula v=w0 would supply a singleton world predicate, which is not clopen. Earlier Gallin expansions in §13 had supported worlds and do not suffer this obstruction.

## 31. A generic Boolean Henkin model: all modalized relational choice and finite evaluators without Plenitude

The generic externalization in this section was developed in this lane and independently audited and sharpened in the parent, algebraic, and world-representation lanes. The underlying full Boolean-valued hierarchy and the truth-choice relation below are already recorded in `topics/classicism/writeups/full-boolean-valued-atom-and-atomless.md`, especially §6. That write-up identifies Andrew Bacon, *Could the truths of mathematics have been different?*, draft of 9 October 2025, online appendix §B.2, pp.7–9 (PDF pp.41–43), as its construction source. The elementary-substructure/generic-world realization and added verdicts here are additional arguments (`misc` if recorded), not a claim to have invented the Boolean hierarchy or truth-choice relation. This is a direct construction in ordinary ZFC, not an assumption that a transitive set model of ZFC exists. It is not a literature-novelty claim. The detailed evaluator comparison is also recorded in the world-representation report. The purpose here is to verify closure and distinguish relational graph selection from representation by operations.

### 31.1 The ambient Boolean hierarchy and elementary substructure

Fix an atomless complete Boolean algebra B, for example the regular-open algebra of Cantor space. Define full set domains A_e=N, A_t=B, and A_{στ} to be the set of all functions A_σ→A_τ, for each original allowed arrow type (τ≠e). Include the full domains of all standard finite types. Choose a regular θ larger than the hereditary sizes of these domains, their powersets needed at the next finite types, and the Boolean operations. For example a successor cardinal strictly above beth_ω(|B|+aleph_0) is more than sufficient after including the chosen concrete presentations. Then all relevant objects lie in H_θ.

By downward Löwenheim–Skolem choose a countable M≺H_θ containing B, its Boolean operations, and every A_σ as parameters. Put D_σ=M∩A_σ. Interpret f∈D_{στ} on D_σ by ordinary evaluation. Closure follows because f,x∈M imply the uniquely defined f(x)∈M. Distinct f,g∈M remain distinct after restriction: if f≠g, H_θ has an argument x with f(x)≠g(x), so elementarity supplies such an x∈M. Repeated application gives the same assertion at every flattened relational type.

All subsequent uses of a full-domain operation or witness are justified in two steps: its size puts it in H_θ, and elementarity supplies an M-witness whenever the parameters lie in M. This includes lambda functions, Boolean family joins/meets, antichain selector graphs, and ordinary ultrafilters on B. It does not make D_σ externally full.

### 31.2 Worlds and the generic truth lemma

Let B_M=B∩M. A world is an ultrafilter G on B_M meeting D∩M for every D∈M which is a dense subset of B\{0}. Such ultrafilters exist through every nonzero b∈B_M: enumerate the countably many dense sets and the usual Boolean decision requirements, choose successively stronger conditions in M by elementarity, and extend the generated filter. Let W be the set of all these worlds, with universal S5 accessibility. Alternatively, choose just one generic G_b through each nonzero b∈B_M; this gives a countable world set with all the same verifications below. Interpret b∈D_t as the truth set {G∈W:b∈G}.

For a family f:A_σ→B in M let q=join_{x∈A_σ}f(x), which belongs M. The set

    D_f={a>0 : a<=not q or there is x∈A_σ with a<=f(x)}

is dense and belongs M. If q∈G, genericity gives a∈G∩D_f∩M; its first alternative is impossible. Elementarity gives an x∈M witnessing the second alternative, and then f(x)∈G. Conversely any f(x)∈G implies q∈G. Thus

    q∈G iff there is x∈D_σ with f(x)∈G.

The dual statement identifies the full-domain Boolean meet with actual universal quantification over D_σ at every generic world. This is the essential point: the joins/meets used are those of M-coded families, not arbitrary external families of elements of B_M.

Every nonzero b has a generic world containing it, so b is true at every world exactly when b=1. Consequently the modal operation is the admitted M-function Box(b)=1 if b=1 and 0 otherwise. Distinct Boolean elements have distinct truth sets, by applying the same observation to their symmetric difference.

### 31.3 Comprehension, lambda, identity, and C

Evaluate formulas recursively by the Boolean operations, the just-described joins/meets for quantifiers, and Box. For every finite formula with M-parameters, its Boolean denotation and every lambda abstraction belong to M by definability and elementarity. The generic truth lemma proves that these denotations agree with the ordinary Kripke truth clauses on W. This handles arbitrary typed quantifier alternation, application and lambda bodies; it does not restrict quantification to a smaller image of transported inputs.

Identity is actual equality of the underlying M-objects. Its rigid singleton predicates, with values 0 and 1, belong to the hierarchy. Hence identity and distinctness are necessary, and all Barcan instances hold because the externalized type domains are constant across W. Relational Intensionality also holds: necessary coextension makes the Boolean agreement value 1 at every admitted tuple; if two M-functions differed, elementarity would supply an admitted tuple witnessing that difference. They are therefore equal.

These facts give a constant-domain intensional Henkin model of H with the required Intensionality/Logical-Equivalence condition of C. In particular, an H-theorem of coextension holds at every generic world and every admitted valuation; the preceding separation argument identifies the corresponding relational intensions. No optional premise is necessitated in this verification. Thus C5 and every boxed Barcan instance hold. The individual domain is the standard N. The rigid successor graph belongs to M and is an injective nonsurjective self-map, supplying quantified individual Infinity by the ordinary internal finite-cardinality induction. The standard finite-cardinality class is also available, but is not needed for this witness.

### 31.4 All modalized relational choice, and hence boxed RC and all IC

Let R∈D_{σρt} be necessarily serial. Its Boolean row joins are 1. This assertion first follows on M-arguments from the generic truth lemma; a failing ambient row would have an M-witness by elementarity, so it holds on every full A_σ row. In the ambient full hierarchy, for each x∈A_σ choose a maximal antichain A_x of nonzero elements refining the row {R(x,y):y∈A_ρ}; its join is 1. Choose, for each a∈A_x, a witness y_{x,a} with a<=R(x,y_{x,a}), and define

    S(x,y)=join{a∈A_x:y_{x,a}=y}.

The entire family and S exist in H_θ; with R as parameter, elementarity supplies such an S∈M. Its rows are pairwise disjoint, their joins are 1, and S(x,y)<=R(x,y). The generic truth lemma therefore makes S a necessarily functional relation below R. This is precisely the recorded Modalized Relational Choice schema, at every input/output type, including individual outputs represented by graphs. The same proof applies at every world, so its boxed schema holds.

For clarity, local Relational Choice follows directly too. Given R serial at a world G, let b=meet_x join_y R(x,y); then b∈G. Refine the rows below b, and place a fixed default output on not b. The resulting S is necessarily functional and obeys b and S(x,y) <= R(x,y). Thus at G it is a functional subrelation of R. This verifies the current/local inclusion convention of RC and proves □RC. The empty-input case gives all IC; alternatively it is the one-row antichain construction.

This maximum principle chooses Boolean-valued RELATIONS. It does not produce an operation whose output object is identical to the selected object at a particular generic world.

### 31.5 Uniform finite Boolean evaluators

For every nonzero b∈B, ordinary AC supplies an ultrafilter V_b on B containing b. Choose the entire family inside H_θ and then in M by elementarity. Define

    E_b(p)=1 if p∈V_b, and 0 otherwise.

Each E_b is an admitted bivalent operation preserving complements and finite Boolean meets, with E_b(b)=1. The family b↦E_b is itself an admitted operation (use any fixed ultrafilter at b=0). Hence finite Boolean evaluator density holds, and even has a single uniformly selecting operation. All these identities are world-independent and hold necessarily.

These evaluator ultrafilters are not worlds: an M-ultrafilter on an atomless B cannot be M-generic. This is exactly how finite evaluator density coexists with a noncompact generic truth space. Their failure of quantifier preservation is explicit. For E=E_V put F(p)=(E(p)→p). Every E(F(p)) equals 1, but meet_p F(p)=meet V=0: any nonzero lower bound of all members of the ultrafilter would decide every Boolean element and hence be an atom. Therefore E(forall p Fp)=0 while forall p E(Fp)=1. The evaluator fails even the current quantifier biconditional, not merely its object-identity strengthening.

### 31.6 Explicit failure of Plenitude and Functional Choice at (t,t)

Define the admitted relation

    U(p,q) := (p and q=top) or (not p and q=bottom).

It is necessarily total and single-valued, selecting the two-valued truth answer for each proposition at each world. Suppose X:tt represented U at a generic world G. Then for every p∈B_M, X(p) is 1 or 0 and equals 1 exactly when p∈G.

By elementarity, X maps the full B into {0,1}; otherwise an M-argument would witness failure. Put V={b∈B:X(b)=1}, an element of M. Its trace on B_M is G. Since G is an ultrafilter, every finite ultrafilter law for V holds on M-arguments; any failure in the full B would again have an M-witness. Thus V is an ordinary ultrafilter on B.

The set B^+\V is dense: below any nonzero b∉V use b; below b∈V split b into two nonzero disjoint pieces and use the piece outside V. This dense set belongs M. Genericity therefore forces G to contain an element outside V, contradicting G=V∩M. No such X exists.

The same U works at every world. Hence □¬Plenitude_{t,t} and □¬FunctionalChoice_{t,t} hold, even while every boxed RC/IC/MRC schema above holds. An alternative verification uses the already recorded §6 calculation directly: for each ambient X:B→B, c_X=meet_p U(p,Xp) decides every Boolean p, so a nonzero c_X would be an atom. Atomlessness therefore makes c_X=0; the generic truth lemma transfers that exact zero value to failure of every admitted operation. The owning write-up calculates the general value as the join of all atoms. This calculation is prior recorded evidence, not a new result of the present notes.

Every relational Boolean algebra in the new model is atomless, not only D_t. If F at flattened type α_1...α_n t is nonzero, elementarity supplies an admitted tuple a with F(a)=b≠0. Choose c∈M with 0<c<b. The relation which has Boolean value c exactly on that tuple and 0 elsewhere is admitted, nonzero, and properly below F. For n=0 this is simply atomlessness of B_M. Thus T fails independently of the explicit witness, at every relational atomicity instance.

### 31.7 Choice on rigid coded fields

An admitted relation is rigid exactly when each of its Boolean values on admitted arguments is 0 or 1. By elementarity this is equivalent to the same assertion on the corresponding full domains. It therefore codes an ordinary relation in H_θ. For a serial rigid relation, ordinary AC supplies a selector in the full hierarchy, and elementarity returns the selector to M. When the output type is relational this selector is an admitted operation with the required object-identical output; for individual outputs it is an admitted graph.

The same argument gives the internal Boolean Prime Ideal Theorem for admitted rigid Boolean algebras and filters: their rigid codes describe actual Boolean-algebra/filter data in H_θ, ordinary AC supplies a proper ultrafilter extension, and its code lies in the appropriate finite type and is returned to M. Only this explicitly rigid, typed interpretation is asserted. There is no assertion that arbitrary external families or external Boolean algebras are represented.

Thus adding strong choice on the rigid typed structure, all interworld choice, and uniform finite Boolean evaluator density still does not supply the missing representation of locally functional relations. The exact obstruction is exhibited by U above, rather than inferred merely from an unproved nonimplication.


**Scope of infinitary additions.** The elementary-substructure construction above establishes the original finitary C result. It does not by itself admit arbitrary external countable lists of M-parameters. A separate relative forcing repair, developed in the parent/world lanes, uses a countably closed ground forcing P of countable partial functions ω_1→2, its complete atomless regular-open algebra B, and the full-support product of cones P↓p_b for chosen p_b≤b, b∈B⁺. Coordinate generics supply a world through every ground nonzero b. The product is countably closed by coordinatewise unions, so it adds no countable sequences of ground objects; every countable formula/parameter code over the ground finite-type domains is therefore already ground. Ground Boolean completeness and the same generic truth lemma give closure under countable conjunctions/disjunctions and their lambda bodies with countably many parameters. This is an explicitly relative forcing construction for that specified extended syntax, with ordinary finite quantifier strings; it is not an arbitrary set-sized infinitary claim or an assertion that the earlier countable M is externally countably complete.
