# Pure Maximalism: structural strengthening and Strong Possibility audit

Research notes, OpenAI Codex, 22 October 2026. Ordinary mathematics only; no Lean claim and no independent human check. These notes do not edit the database. The fixed finitary reference theory is the repository's relational-type Classicism C. Optional enrichments are explicitly marked.

**Consolidation status, 22 October, afternoon.** This is the early orientation note, not the final proof collection. The detailed audited arguments are in `profile-root-construction-20261022.md` (atomic-cell criterion, signature obstruction, finite and non-Fregean examples), `reflection-universal-core-20261022.md` (SP = universal identity maximality, disjunction/embedding criteria, no strong worlds), `reflection-retract-fragments-20261022.md` (simultaneously consistent large SP fragments), `complete-theories-finite-bounds-20261022.md` (standard necessary finite bounds for complete effective theories), and `infinitary-standard-numerals-20261022.md` (explicit changed-logic obstruction). All paths are relative to `.reproduction/classicism-research/`. Section 7 below remains a provisional construction and is not among the audited conclusions. Full finitary pure-SP consistency remains unsettled by this work.

## 1. Source and recorded evidence

Read `topics/classicism/topic.yaml`, the Framework/Notation/Conventions portions of `background.md`, the pure/signature Maximalism and Strong Possibility records, the coalesced model records and associated definitions. Proved-only `load_topic`/`Engine` queries confirm: pure Max has recorded models with Actuality and without Actuality, with BF and without BF; no recorded entailment of either; pure Strong Possibility implies pure Max. The recorded monism argument is Cian Dorr's 16 October 2026 argument in `results/strong-possibility-and-infinity-e-incompatible.yaml`, not a discovery of this research.

Direct accessible primary source: Bacon–Dorr, *Classicism*, https://andrew-bacon.github.io/papers/Classicism.pdf is the **1 July 2022**, 85-page draft. It is not the database's 16 May 2023, 87-page draft. Appendix E's page numbers differ (2022: pp. 78–81; database: pp. 80–83). PhilPapers' indexed 2023 PDF returned 403. Construction references below use the database's exact descriptions unless otherwise stated.

## 2. A transparent equivalent formulation of Strong Possibility

Write H for the distinctness-preserving necessity, H p := ∃q(q ∧ □(◇q→p)), and D for its dual. Classical quantifier and modal duality gives

    D p ↔ ∀q (q → ◇(p ∧ ◇q)).

Thus Strong Possibility says: for every pure P consistent with Max(C), each actual truth q is possible from some possible P-state. Equivalently, every **finite** family of actual truths can remain jointly possible at some P-state: use their conjunction as q. The chosen P-state can depend on q. This is not a common witness for all actual truths, nor an assertion that P can coexist with all actual truths.

This reformulation is an equivalence in C and is more transparent than a negated existential definition. It changes neither the fixed reference Max(C) nor the language restriction.

## 3. Monism, and immediate local obstructions

Let E1 := ∀x^e∀y^e(x=y). Max(C)+E1 is consistent by the recorded singleton-individual coalesced root. If a≠b actually, q := a≠b is true. NI yields the C-theorem ◇(a≠b)→a≠b. Necessitating the appropriate universal instance gives □(◇q→¬E1); hence H¬E1. Therefore C proves D E1→E1. Strong Possibility supplies D E1, and C has nonempty e, so pure Strong Possibility entails exactly one individual.

**New local corollary: unboxed BF at e is impossible under pure SP.** Pick the sole individual a. For every actual x, x=a, and NI gives □(x=a). Thus ∀x□(x=a). BF at e yields □∀x(x=a), hence □E1. Pure SP implies pure Max, which gives ◇¬E1 since two individuals are C-consistent. Contradiction. Only the e instance of unboxed BF is used.

**New local corollary: unboxed Functionality e→t is impossible under pure SP.** Put h:=λx^e(x=a) and u:=λx^e⊤. For each actual x, NI gives (x=a)=⊤, so hx=ux as propositions. Functionality gives h=u. Substitution and the necessary coextensionality consequence of relation identity give □∀x(x=a), contradicting pure Max as above. This gives explicit distinct properties with the same propositional value at every actual individual in any hypothetical pure-SP model.

## 4. The signature issue is not a harmless restriction of instances

Suppose Σ contains a relational constant c of type τ. If a model of pure SP exists, expand it by interpreting c as ⊤τ. Pure SP, being pure, is preserved. But signature Max entails c≠⊤τ: C(Σ) does not prove c=⊤τ, since c can instead be interpreted as ⊥τ. Signature SP implies signature Max, so it fails in this expansion.

Consequently, the unconditional theorem

    C(Σ)+SP_pure ⊢ SP_Σ

for arbitrary interpretations of a nonempty relational signature would imply that pure SP is inconsistent. Conversely inconsistency would imply the theorem by explosion.

**Stronger result obtained later:** even existential expansion to signature Max is impossible. Pure SP forces the finite one-individual Fregean cell A1 to be an atom. For any admitted relational constant c, its universal closure R(c) can be either true or false in that cell. Signature Max makes both A1∧R(c) and A1∧¬R(c) nonbottom, splitting A1. Hence pure SP and Max(C(Σ)) are jointly inconsistent for every admitted signature Σ. See `profile-root-construction-20261022.md`, section 9, for the complete proof. The earlier arbitrary-interpretation observation alone was weaker and did not establish this.

For the converse, adding individual constants produces a direct reference-theory obstruction. If Σ contains at least two e constants c,d, Max(C(Σ)) entails c≠d, so its reduct cannot satisfy E1. But E1 is consistent with pure Max. Hence conservativity of Max(C(Σ)) over pure Max already fails. This alone is not a countermodel to SP_Σ→SP_pure: either SP could still be inconsistent. The database note's asserted 'iff' between the implication and conservativity is too strong; conservativity suffices for direct instance restriction but is not a necessary condition for arbitrary derivability, especially under possible inconsistency.

## 5. Finite signatures determine their own individual cardinality

Suppose Σ has exactly m≥1 individual constants c1,…,cm, with any set of relational constants. Let

    Exhaust_m := ∀x^e (x=c1 ∨ ... ∨ x=cm).

Max(C(Σ))+Exhaust_m has a coalesced model: take a C(Σ)-complete family; use the m names as the root's individuals, with each distinguished arrow sending name ci to that component's interpretation of ci; glue relational constants and use compatibility-full root relational domains. Every C(Σ)-consistent sentence holds in a component, while the root has precisely those m individuals. This is the finite version of Appendix E's constant-indexed alternative root; nothing requires distinct interpretations in the components.

If an actual a lies outside the names, let q:=∧i(a≠ci). It is true. At any accessible state where ◇q holds, each ◇(a≠ci) holds, hence a≠ci by NI, so Exhaust_m fails there. Thus H¬Exhaust_m, proving C(Σ)⊢D Exhaust_m→Exhaust_m. SP_Σ therefore forces Exhaust_m. Max(C(Σ)) also forces pairwise distinct names, so SP_Σ entails exactly m individuals. With no e constants the singleton construction gives E1; with one constant named exhaustion is E1.

It follows that SP_Σ and SP_(Σ plus a fresh individual constant) are incompatible when m≥1 is finite. Pure SP and SP_Σ with m≥2 are incompatible. These are joint-inconsistency statements; they do not establish individual inconsistency.

The BF_e and Functionality e→t obstructions generalize: Exhaust_m yields ∀x□(∨i x=ci), so BF_e yields necessary exhaustion, contradicted by signature Max's possible extra individual. Functionality applies to the finite join of the named haecceities and the universal property.

## 6. A general reflection lemma for universal equality diagrams

Let θ(x̄) be a finite Boolean combination of equality atoms Ai(x̄)=Bi(x̄), with arbitrary well-typed terms and any fixed parameters. Let U:=∀x̄ θ(x̄). Then C proves

    D U → U.

Proof. If U fails, select actual witnesses ā. Record the finite truth diagram of all equality atoms at ā. Every true equality is necessary by NI. Let q be the conjunction of the inequalities corresponding to the false equality atoms (⊤ if there are none). Then q is actually true. At every accessible state, all the positive equalities hold. If ◇q holds there, each negative equality remains negative by the theorem ◇(A≠B)→A≠B. Hence that state has the same finite equality diagram, so ¬θ(ā) and ¬U hold. Thus □(◇q→¬U), and H¬U. Contraposition proves the claim.

In particular the lemma covers universal Horn quasi-identities and universal disjunctions of identities. Therefore SP forces every such **pure** universal law that is consistent with Max(C). Finding finitely many individually Max-consistent laws in this class whose conjunction is Max-inconsistent would refute pure SP. No such family has yet been proved here. Substituting arbitrary truth atoms for equality atoms is invalid: ordinary truth need not persist.

## 7. A new consistent richness strengthening of pure Max (construction candidate)

This construction is distinct from the SP work and tests the claim that Max has no natural consistent strengthenings.

Use the recorded finitely pinned interpretation-arrow coalesced root, with a countably infinite set of individual names, but **uncountably many propositional names**. Components are a set of action models complete for pure C. The root has an arrow (V,I) to every component object under every interpretation of all names. Relational root intensions have finite name support and component transports in the component domains; root identity-arrow extensions are unconstrained. The usual term-closure proof and fresh-name BF proof are unchanged by enlarging the supply of names. The root satisfies pure Max, Actuality, BF, and local relational/transversal choice (with the customary metatheoretic choice assumptions).

Claim: every root family X of false nonbottom propositions whose cardinality is at most that of the root individual domain has a single proposition splitting every member of X. Formally, if X injects into e by an actual injective relation, there exists q such that for every p with Xp and ¬p and p≠⊥,

    p∧q ≠ ⊥  and  p∧¬q ≠ ⊥.

Proof. X is externally countable because root e is countable. The union of the finite supports of its members is countable. Choose a propositional name c outside that union. Let q be false at the root identity and, on component arrows, say that I(c)=⊤. This is a finitely pinned admissible proposition; transports are identities to ⊤ in the corresponding component. Any possible false p is true at some component arrow (V,I). Changing only I(c) to ⊤ or ⊥ keeps p true and respectively makes q true or false. Thus both pieces are nonbottom.

This is a simultaneous-splitting/reaping-number principle, stronger than merely splitting each false nonbottom proposition. It must exclude the actual atom supplied by Actuality, which cannot split. A strictness witness should use the countable-name version and a countable basis of cylinders over a singleton extensional component; that proof is not yet fully written. The enlarged-name consistency argument appears sound but awaits independent audit; do not promote it to a database record from this note alone.

## 8. Infinitary resources: an elementary obstruction and a warning

If an enrichment supplies **all semantic set-indexed conjunctions of propositions**, with conjunction true exactly when every conjunct is true and with the ordinary meet property, every state has a strongest truth: conjoin the set of all its true propositions. If this closure is imposed at every state, □Actuality follows. Old pure Max(C) supplies ◇¬Actuality, so it is inconsistent with this enrichment.

This argument concerns semantic full set-indexed closure. It is not a proof about ordinary finitary C, nor automatically about the syntactic language L_(ω1,ω), which does not give a conjunction of an arbitrary semantic family. Replacing Max(C) by Max of the stronger infinitary theory changes the consistency side condition and invalidates the old counterinstance unless separately re-established.

The separately audited note `infinitary-standard-numerals-20261022.md` gives a stronger obstruction for countable disjunction under lambda abstraction, with explicit semantics and fixed old Max(C). It uses the standard-numeral predicate and arithmetic incompleteness. This remains a changed-logic argument; no contradiction of finitary pure SP has been established.
