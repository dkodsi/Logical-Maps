# Explicit-world choice and descriptions

Original research, OpenAI Codex, 22 October 2026. No human or Lean check claimed. Fixed framework C, relational types; T=C+□Functional Choice. The Gallin interpretation here is an interpretation with an explicit world argument, not permission to add a rigid term meaning the current world.

## 1. Definitions

For a proposition a and a property P of type τt, write

    Sat(a,P,y) := a≤Py := □(a→Py).
    Inhab(a,P) := ∃y Sat(a,P,y).
    Unique(a,P) := ∃y[Sat(a,P,y) ∧ ∀z(Sat(a,P,z)→z=y)].

An actual atom a serves as a world index. Sat says that y satisfies P at that atom. Define the following schemas, for relational τ≠e:

    WC_τ := ∃E^{t(τt)τ} □∀a^t P^{τt}
              [(Atom_t(a)∧Inhab(a,P))→Sat(a,P,(Ea)P)].

    WD_τ := ∃D^{t(τt)τ} □∀a^t P^{τt}
              [(Atom_t(a)∧Unique(a,P))→Sat(a,P,(Da)P)].

These assert one operation obeying a necessary world-indexed law. They are genuinely ∃E□laws, not merely □∃E laws. Parentheses in applications follow the repository convention.

## 2. Characterizations

Over C, as schemas at all relational output types,

    □Functional Choice  ↔  □Actuality + WC.
    □Plenitude          ↔  □Actuality + WD.

The right sides use the original Actuality and original atoms, not an added primitive world type. The operation-input type σ of ordinary choice need not appear in WC/WD, because a binary relation U is fed to E through its property-valued row x↦λy.Uxy.

### Forward choice direction

T implies □ND and □BF. Every equality proposition, and every quantified formula built from equality propositions, is settled; NI+ND give the atomic case and BF gives universal and existential closure. Thus Atom(a), Sat(a,P,y), Inhab(a,P), and Unique(a,P) are settled.

Form the serial relation on the pair (a,P) and y:

    [(Atom(a)∧Inhab(a,P))∧Sat(a,P,y)]
      ∨ [¬(Atom(a)∧Inhab(a,P))∧y=⊥_τ].

Functional Choice gives E selecting a y for each pair. Its selection law is built from equality propositions, so each instance of that law is necessary. BF at the two input types gives the displayed boxed universal law. This is not illicit necessitation of an optional premise. T also implies □Actuality.

### Forward unique-description direction

Under □Plenitude use the same construction, replacing Inhab by Unique. The relation is now functional, so Plenitude represents it. The same NI+ND+BF argument gives a single D satisfying the boxed law, and □Actuality is already a consequence.

### Converse at a point

Actuality supplies a true proposition a that entails every truth. In C such an a is an atom: if 0<b≤a, then either b is true and Actuality gives a≤b, or ¬b is true and Actuality gives a≤¬b, forcing b=0. Thus, for every actual p,

    a≤p iff p.

Let U^{στt} be serial. For each x, the property P_x:=λy.Uxy satisfies Inhab(a,P_x). Set f x:=(Ea)P_x. WC gives a≤U(x,fx), hence U(x,fx), so f witnesses Functional Choice.

If U is functional, Unique(a,P_x) holds instead. Using D in the same formula gives Plenitude.

For the boxed conclusions, run this pointwise argument at every accessible point using □Actuality and the ONE transported operation with its boxed law. Equivalently, necessitate the discharged C derivation of the pointwise implication, then apply K and the boxed hypotheses. No □ND, BF, or choice is assumed in this converse: those are obtained only after □FC or □Plenitude has been derived.

## 3. Stronger event-indexed form comes for free

The atom restriction can be omitted from both forward constructions. T supplies a single E such that

    □∀a,P [Inhab(a,P)→Sat(a,P,(Ea)P)],

and □Plenitude supplies the analogous unique-witness operator. Thus a may name any information state/event: if one fixed entity satisfies P throughout a, the operation picks such an entity. With □Actuality these stronger versions have the same converses and hence the same characterizations.

This does not infer a uniform witness from □∃y Py. Its antecedent is ∃y□(a→Py), and that scope is indispensable.

## 4. Individuals and the type restriction

There is no operation type ending in e. Therefore no E:t(et)e has been introduced. For individual-valued choice, return haecceity codes H_y:=λz.z=y, of type et. Apply the preceding choice construction with relational output et to the relation

    ∃y^e[Q=H_y ∧ Sat(a,P,y)].

Here the choice construction means applying Functional Choice directly to the displayed code-valued relation, with the same default-value totalization as above; equivalently instantiate the indexed operator with the corresponding property of codes. The chosen Q uniquely identifies y because haecceity coding is injective in C. Equivalently, use a functional relation selecting the individual, rather than a forbidden operation. The same coding works uniformly at every type if a single output convention is wanted.

## 5. Why an explicit world argument matters

A current-world choice/description operator with ONE necessary unindexed law has a different scope and can collapse the modality. The parent lane has independently established the necessary-unique-witness collapse. WC/WD avoid that collapse by selecting relative to the atom a passed as an argument. They remain valid in every full S5 model with multiple worlds.

There is no closed pure term that picks the current true atom in a nontrivial model and tracks it as the evaluation changes. If such a term A had □[Atom(A)∧A], then A would be a necessary true atom, so A=⊤ and ⊤ would be an atom; the proposition algebra would have only ⊥ and ⊤. Choosing a true atom at an evaluation is existentially valid; naming that choice rigidly as the moving evaluation is not.

In a full Gallin presentation, worlds form an explicit set W, original propositions are predicates W→2, and an indexed choice operation may be written E(w,P). Ordinary extensional set-theoretic choice then supplies a witness in {y:P(y,w)}. The intensional internal formulas above are exactly this construction using atom codes for w. Infinity of W or of the individual set causes no difficulty; take, for example, D=N and W=P(N) with the full hierarchy.

## 6. Relation to the wider research

This characterization complements the root world–tuple/Gallin representation. It isolates the extra selection content of □Functional Choice beyond □Plenitude: global choice becomes coherent after the world of evaluation is supplied explicitly. It also gives a precise policy for adding familiar logical resources: world-indexed descriptions and selection are supported, while an unindexed necessarily correct current-truth description operator is stronger and generally collapses contingency.

All new equivalences here should be attributed to misc if integrated. Recorded inputs are the Plenitude consequences □ND, □BF and □Actuality (Bacon–Dorr, Classicism §§2.1–2.3, pp.21–34 in the 16 May 2023 draft) and the fixed definitions in Background. The new characterizations themselves are not attributed to the paper.

## 7. Naming a logical selector: atom inputs and event inputs diverge

Sections 2–3 concern existential axioms: an appropriate selector exists. A separate question arises if a witnessing operation is named by a new logical constant E and No Pure Contingency is extended to the enlarged language. This extension of purity is an additional assumption, not a consequence of the old pure schema. Under that assumption the atom-indexed and event-indexed laws differ sharply.

### 7.1 A named event selector collapses contingency under enlarged NPC

Use the output-t event selector and the closed property P:=λy.Atom_t(y). Under T, there is an atom whose atomhood is necessary: atomhood is settled by NI, ND, and BF, and Actuality supplies an actual atom. Hence Inhab(top,P). The named event law gives, for the closed enlarged-language term

    b := (E top)(λy.Atom_t(y)),

the condition □Atom_t(b). In particular b is nonbottom, so ◇b. Enlarged No Pure Contingency applied to ¬b gives ◇b→b; applied to b it gives b→□b. Consequently b=top, and top is an atom. Every proposition is therefore bottom or top, giving the Fregean Axiom and hence Extensionality in C.

Thus T, the named event law, and enlarged NPC imply Extensionality. The existential event-selection axiom alone does not do so: it is already a consequence of T. The issue is naming a witness as logical while extending purity to all formulas mentioning it.

### 7.2 Named atom selectors preserve nontrivial enlarged NPC

Take the full S5 hierarchy with worlds W=C2={0,1}, singleton individuals, and all admitted set-functions. The group C2 acts on propositions by swapping the two worlds, acts trivially on individuals, and acts on arrow types by conjugation:

    (g·f)(x) := g·f(g⁻¹·x).

Application, identity, Boolean operations, and full quantification are equivariant. This is a full finite hierarchy at each fixed type, so it satisfies T. The two world atoms form a free transitive C2-set.

For every relational output type τ, choose in the metatheory a witness selector c_τ(P) at the reference atom a0: whenever Inhab(a0,P), it satisfies a0≤P(c_τ(P)); otherwise give it bottom_τ. Define an operation on atom inputs by

    E_τ(a_g,P) := g·c_τ(g⁻¹·P).

For nonatomic inputs a, define E_τ(a,P):=bottom_τ. The element g taking a0 to a_g is unique, so the formula defines an actual set-function, represented by the full operation domain. Equivariance of application and order proves the atom-indexed selection law. Moreover

    E_τ(h·a,h·P)=h·E_τ(a,P).

Thus every E_τ is fixed as an operation entity by the same C2 action. Naming all these operations still leaves a transitive action by automorphisms on worlds. Every closed sentence of the enlarged pure language has a C2-invariant truth set, hence is either true everywhere or false everywhere: enlarged NPC holds. Extensionality fails because either singleton world proposition is contingent.

The construction's reference atom a0 and choices c_τ are not named in the logical language. Only the equivariant operations E_τ are named. The law holds necessarily because in this full S5 hierarchy the atom, order, and inhabitation tests are settled.

This proves consistency of T plus named atom selectors and enlarged NPC with nontrivial contingency. It also identifies why the same equivariant construction cannot handle all event inputs: top is fixed by the group, as is the property of being an atom, while neither atom is fixed. An event selector on that input must break the transitive symmetry.

The homogeneity lane independently checked the modal scope, conjugation action, and expanded-purity argument. A small exhaustive check at output type t is saved in `check-named-atom-selector.py`; it checks all 256 properties of the four proposition entities and all four event inputs. This finite check supplements the all-type mathematical argument; it is not its proof.

The countermodel also permits arbitrary well-founded set-indexed pure conjunctions and disjunctions, with parameterized lambda closure. These truth operations commute with the group action, and each full finite type contains every resulting denotation. Thus the transitive-automorphism proof of enlarged NPC survives those infinitary resources. No world atom is introduced as an additional logical constant.

## 8. Exact symmetry criterion for named selection resources

This is a semantic result about FULL S5 hierarchies and their automorphisms, not an additional theorem of bare C. Let G act faithfully by logical and application-preserving automorphisms, and let A be a prescribed G-invariant family of nonzero proposition-events. Assume the ordinary metatheoretic choices needed to select orbit representatives and witnesses. There are G-equivariant selector operations at all admitted relational output types satisfying the event law on A if and only if the action of G on A is free.

### Necessity

Suppose h≠1 fixes an event a∈A. Faithfulness supplies an entity y moved by h. It may be taken at a relational type: if an individual is moved, its haecceity is moved too. The cyclic orbit

    O := {h^n·y : n∈Z}

has no h-fixed member. By fullness its rigid characteristic property P exists, with Pz=top on O and bottom elsewhere. P is fixed by h. Because a is nonzero, Sat(a,P,z) holds exactly for z∈O. The selector law therefore puts E(a,P) in O, whereas equivariance and the fixed inputs force h·E(a,P)=E(a,P), a contradiction.

The orbit predicate need not be pure-definable; the selector law quantifies over all properties, and fullness supplies this one. Without faithfulness the exact criterion is that the stabilizer of every a∈A acts trivially on the whole hierarchy, or equivalently that the effective quotient group acts freely on A.

### Sufficiency

Choose one reference event a_i in each A-orbit and a witness selector c_i at that event for each output type, defaulting to bottom when no witness exists. Every a∈A has a unique expression g·a_i. Define

    E(g·a_i,P):=g·c_i(g⁻¹·P).

Uniqueness makes the definition unambiguous. Equivariance of application and order verifies both the selection law and equivariance of E. Use bottom outside A. The zero event may be included separately with this same default: Sat(bottom,P,y) is vacuously true, so zero imposes no obstruction. Nonzero top is different; it is fixed by every group element and obstructs any nontrivial faithful action.

### Consequences

For W=C_p with p prime and translations acting on the full hierarchy, the family of all nonzero proper events is free. Every nonidentity translation generates C_p, so an invariant nonempty subset would have to be all of W. Consequently selectors for ALL proper events can be named while retaining transitive symmetry and enlarged NPC, including in the infinitary extension just described. Requiring the law also at top produces the collapse in §7.1.

Named atom selectors force every residual automorphism fixing a world to be the identity, by the same orbit argument. Hence if a regular transitive group G was used in their equivariant construction, the full residual automorphism group is exactly G: any residual automorphism agrees with some g∈G at one world, and its composition with g⁻¹ fixes that world. Logical choice can therefore remove stabilizers while retaining a nontrivial transitive world symmetry.

For this last freeness obstruction, a selector at output type et alone suffices in a full hierarchy. Its domain detects world permutations through constant unary predicates and individual permutations through haecceities; all higher-type actions are then determined by application. The all-type formulation above is retained for its direct connection to the choice schema.

The homogeneity lane independently audited the orbit predicate, zero-event exception, faithfulness condition, transport construction, and infinitary scope. These are new arguments in this report; no published-source attribution or human check is claimed.

## 9. Finite classification for proper-event choice and enlarged NPC

In a full S5 hierarchy with singleton individuals and exactly n worlds, there EXISTS a named output-t selector E satisfying the law for every nonzero proper event and enlarged No Pure Contingency if and only if n=1 or n is prime. This is an existence classification in this exact class of full finite models. It does not say that every selector on a prime-sized world set satisfies enlarged NPC.

### Finite orbit definability

For any specified E in this model, let G be its logical automorphism group. Every G-orbit of world atoms is definable by a closed sentence of the pure language enlarged by E.

To see this, fix metatheoretic enumerations of the finite domains D_t and D_tt. A finite diagram says that variables p_1,…,p_m and F_1,…,F_k enumerate these domains exhaustively and without repetition; it records their complete Boolean-operation tables, the complete application table (F_i)p_j, and the complete E-table (E p_i)F_j. All entries are equations between the enumerated proposition variables or the fixed Boolean constants. For an atom at index r in the reference enumeration, form the closed sentence

    ∃p_1…p_m F_1…F_k (Diagram_E(p̄,F̄) ∧ p_r).

The diagram itself is settled. Any satisfying enumeration gives a Boolean automorphism on D_t. Its action on D_tt is forced by the application table to be conjugation, and the E-table says that it fixes E. Conversely every such Boolean automorphism yields a satisfying enumeration. With singleton individuals it extends through all full higher types by conjugation. Therefore the sentence is true exactly on the G-orbit of the distinguished atom. The reference enumeration and its index r are metatheoretic devices; no world atom is named in the language.

Enlarged NPC now forces every such nonempty orbit to be all worlds. Hence G is transitive. This inference uses the finite table argument and is not a general claim that NPC implies homogeneity in arbitrary models.

### Group-theoretic restriction

Suppose n>1. Proper nonzero events include the world atoms. The orbit obstruction in §8, already at output t because individuals are a singleton, makes G free both on worlds and on all nonzero proper events. Its transitive world action is therefore regular.

If g∈G is nonidentity, any one of its world cycles is a nonempty event fixed by g. It cannot be proper, so g must act as a single n-cycle. In particular G is cyclic, generated by g. If n were composite, a suitable nonidentity proper power of g would have more than one world cycle, contradicting the same requirement. Therefore n is prime.

Conversely, when n is prime, §8's C_n construction supplies equivariant selectors on every nonzero proper event, with bottom defaults at zero and top. Transitivity yields enlarged NPC. When n=1 the proper-event law is vacuous and every sentence is settled. This completes the classification.

The positive models also admit the infinitary extension in §7.2; the negative argument already uses finite formulas. The homogeneity lane independently audited the finite orbit formula, completeness of its type tables, modal scope, and the distinction between existence of a good selector and an arbitrary selector.

For this same finite, full, singleton-individual setting, the three named resources therefore have the following existence spectrum when enlarged NPC is required:

| Required event inputs for the named output-t selector | Possible positive finite numbers of worlds |
| --- | --- |
| Atoms only | Every n≥1, using a regular cyclic action |
| Every nonzero proper event | One, or any prime |
| Every event (or any scope including top) | One |

Each row concerns existence of a suitable named selector, not arbitrary choices of its table. The positive examples continue to satisfy enlarged NPC under the stated infinitary conjunction resources.

## 10. Finite classification under the benchmark, without extra fullness

The negative part of §9 actually holds in EVERY T-model with exactly n externally fixed finite Boolean world atoms. No singleton-individual or independent fullness premise is required. Here n counts proposition atoms, not potentially redundant objects in an action-category presentation of the model.

Atomicity_t and finitely many atoms make every proposition the finite Boolean join of its supporting atoms. Thus D_t is the finite algebra P(n). Functionality injects D_tt into the actual functions D_t→D_t. Conversely each such function is represented by a finite case term

    λx. ∨_i ((x=p_i) ∧ q_i),

where the p_i enumerate propositions and q_i are its required outputs. C5 makes the equality guards crisp, so the outputs are the entities q_i, not merely propositions currently equivalent to them. Hence D_tt is full and finite; the same argument covers the E_t table. BF makes finite exhaustive enumerations necessary, while NI and ND preserve their identities and distinctions.

The diagram in §9 uses only these t/tt/E_t tables. It therefore defines the orbits of the automorphism group of that finite fragment even if a particular fragment automorphism were not known to extend through the remaining Henkin hierarchy. The quantified diagram guard is settled, and its sentence denotes the finite union of its satisfying distinguished atoms. Enlarged NPC forces this fragment group to be transitive. The rigid cyclic-orbit predicates used in the proper-event obstruction are already members of full D_tt. The composite-n contradiction therefore follows without assumptions on the individual domain.

For the positive side one can say more than existence of some model. The Boolean-automorphism extension theorem in `homogeneity-amalgamation-lane.md`, §§1–2, extends every represented Boolean automorphism through all admitted types in C5, fixing individuals. A permutation of a finite atom set is represented by finite cases. When n is prime, use its regular cyclic action and the finite equivariant construction of E_t from §8; the finite table is represented in the model. The extended cyclic action fixes E_t and is transitive on atoms, so pure-term equivariance gives enlarged NPC. Thus every T-model with prime finite atom count admits such a finitary-language expansion. At one atom the conclusion is immediate.

All structural inputs here are already available under □Plenitude; T is retained as the stated benchmark. This refinement concerns the finite case and does not assert that every Henkin model supports arbitrary infinitary lambda terms. The homogeneity lane independently audited the finite-fullness argument, fragment-only negative proof, and model-by-model prime expansion.

## 11. Arbitrary infinitary conjunction already gives a global classification

Consider a SET-SIZED full S5 hierarchy with any nonempty individual domain. Add a named output-t selector E for all nonzero proper events. Allow arbitrary well-founded, set-sized conjunctions/disjunctions and parameterized lambda abstraction with infinitary bodies. Terms may have arbitrary well-founded set-sized formation rank. Extend NPC to this pure language containing E.

Then such an expansion exists exactly when the world set has cardinality one or a finite prime. No set-length quantifier block is needed. This is a semantic theorem about the explicitly enlarged language; it is not a theorem about original finitary C or every fixed bounded L_(κ,ω).

### 11.1 Infinitary terms enumerate propositions relative to an atom

Suppose there is more than one world, so every atom is a nonzero proper event. For an atom variable a define terms by metatheoretic recursion on set ordinals:

    t_α(a) := (E a)(λp. ∧_(β<α) (p≠t_β(a))).

Fix a reference atom a0 in the metatheory. The equality predicates are crisp. As long as some proposition remains outside the earlier values, the selector law makes t_α(a0) a new value. Recursion up to the Hartogs ordinal of B=D_t therefore reaches a first exhaustion stage λ: otherwise it would inject that Hartogs ordinal into B. The values (t_α(a0))_(α<λ) biject λ with B.

This defines actual infinitary terms, not a new sequence constant or a semantic oracle. Each fully expanded term is a set-sized syntax tree. Recursive ordinal indices strictly decrease down branches, so the tree is well-founded. Every subformula has only finitely many free variables. The reference atom and the stage λ choose the later syntax in the metatheory; a0 is never named in the object language.

### 11.2 A parameter-free infinitary sentence defines each world orbit

Let δ<λ be the index for which t_δ(a0)=a0. Define a one-variable formula Θ(a) requiring:

1. the t_α(a), α<λ, are pairwise distinct and cover D_t, the latter expressed by the ordinary single quantifier ∀p ∨_(α<λ)(p=t_α(a));
2. they have the same complete Boolean-operation tables as the reference enumeration t_α(a0), and t_δ(a)=a;
3. they have the same complete E-table as the reference enumeration.

The last clause can also be written with no long quantifier block. For every set-function f:λ→λ define the term

    P_f(a) := λp. ∨_(α<λ) [(p=t_α(a)) ∧ t_(f(α))(a)].

Under the first clause these terms range through ALL functions D_t→D_t. For each α and f, let r(α,f)<λ be the unique reference index with

    (E t_α(a0))(P_f(a0)) = t_(r(α,f))(a0).

Require the corresponding equation

    (E t_α(a))(P_f(a)) = t_(r(α,f))(a)

in Θ. All index collections, including λ^λ, are sets; all object-language quantifier blocks are finite. The tables and indices are metasyntactic data encoded by the pattern of equations, not new semantic parameters.

The matching-index map t_α(a0)↦t_α(a) is then a Boolean automorphism, sends a0 to a, and preserves E by the complete-table clause. Boolean automorphisms of P(W) are world permutations. Conversely any world permutation preserving E commutes with all the terms t_α by well-founded syntax induction, and so carries a0 to an atom satisfying Θ. Therefore

    ∃a (Atom(a) ∧ a ∧ Θ(a))

is a closed pure infinitary sentence defining exactly the orbit of a0 under the WORLD permutations preserving E. This is the effective world-permutation group, not the full automorphism group with a possible kernel of individual permutations. Any such world permutation extends through the full hierarchy by acting identically on individuals and by conjugation at higher types.

The formula is model-dependent, which is legitimate when testing a schema containing every closed sentence of this language. It names no atom, has no hidden infinite quantifier block, and is true at the reference atom.

### 11.3 NPC and proper-event choice leave only one or prime worlds

Enlarged NPC forces the nonempty orbit defined above to be all worlds. Thus the effective world group is transitive. The rigid cyclic-orbit predicate argument in §8 makes it free on every nonzero proper event. If a nonidentity element had a proper world cycle, that cycle would be a nonempty proper event fixed by it, contradiction. Hence every nonidentity element acts as a single world cycle and generates a regular cyclic group.

An infinite cyclic action has the nonidentity square with two proper cycles. A composite finite cyclic action similarly has a nonidentity proper power with multiple cycles. Both are impossible. The world set must therefore have cardinality one or a finite prime. Conversely the prime cyclic models from §8 satisfy the required law and enlarged NPC under arbitrary such infinitary formulas, because the transitive action preserves the new connectives and lambda denotations. This works for any nonempty individual set in the full hierarchy, with the cyclic action trivial on individuals.

The extension and homogeneity lanes independently audited first exhaustion, Hartogs, syntax sizes and well-foundedness, table coding, absence of atom parameters, and the exact quantifier/language scope. No claim is made that countable conjunction alone or a fixed bounded infinitary language supplies the orbit sentence needed for an arbitrary infinite model.

### 11.4 Atom-only choice preserves precisely regular world symmetries

The enumeration and orbit formula in §§11.1–11.2 use only the atom-input law. Consequently, for a named atom-indexed E_t in this full set-sized infinitary setting, enlarged NPC holds exactly when the effective world-permutation group Aut_t(E) acts transitively. The atom-input law already makes every world stabilizer trivial, so equivalently that action is regular. This includes a singleton world set.

Conversely EVERY set-sized abstract group G can occur exactly as Aut_t(E), assuming the metatheoretic choice needed for a reference witness table. Take W=G with regular translations, choose witnesses at the identity atom, and transport them as in §7.2, defaulting to bottom on nonatomic inputs. All translations preserve E. Any residual world automorphism agrees with a unique translation at one world; composing with its inverse fixes that world and hence is the identity by the orbit obstruction. Thus the effective world group is exactly G, and transitivity supplies enlarged NPC.

For arbitrary individual domains this is a statement about the effective WORLD group. Independent individual permutations may remain in the full hierarchy automorphism group's kernel. The homogeneity lane independently checked this realization and the regular-action equivalence. No further restriction on G comes from atom-only selection; the restriction to one or prime worlds arises when selection is also required for all nonzero proper events.
