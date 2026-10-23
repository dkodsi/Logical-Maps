# Structural lane: live handoff index

22 October 2026. Root chat 01a164a4-f326-7161-9eac-b9cf19e5ff50. Scratch mathematics only; no database edits or Lean work. This index distinguishes established arguments from remaining research. It does not claim literature novelty or a human check.

## 1. Existing conjecture resolved by a new argument

**Relational Choice + Boolean Completeness ⇒ Transversal Choice in C.** Exact sufficient instances are RC_(σt,σt) and BC_(σt), for arbitrary σ including e. All hypotheses/conclusion are unboxed.

Full proof: [relational-choice-boolean-completeness-transversal-proof.md](/tmp/classicism-research/relational-choice-boolean-completeness-transversal-proof.md).

Independent audits: [audit-coordinator-modal-scope.md](/tmp/classicism-research/audit-coordinator-modal-scope.md), [audit-bc-partial-selectors.md](/tmp/classicism-research/audit-bc-partial-selectors.md), [audit-bare-c-bourbaki-witt.md](/tmp/classicism-research/audit-bare-c-bourbaki-witt.md), and [INDEPENDENT-AUDIT-REPORT-01a164ea.md](/tmp/classicism-research/INDEPENDENT-AUDIT-REPORT-01a164ea.md) in this directory. The coordinating audit and both component audits pass. The only identified exposition correction, replacing predicate-code equalities C=I/D=I by actual coextension C≡I/D≡I, has been applied.

The argument uses evaluation's right adjoint to preserve represented algebraic joins, partial transversals defined by ∀xy□ (boxes inside quantifiers), a guarded strict extension, and a bare-C fixed-point proof for functional graphs on antisymmetric chain-complete posets. It never identifies coextensive property codes or represents a chosen graph by an operation. A separate final purification gives a transversal satisfying the stronger □∀xy safety condition; that does not alter the pointwise-box scope required in the join proof.

The recorded conjecture is `relational-choice-and-boolean-completeness-imply-transversal-choice`, attributed to Zachary Goodsell, 27 September 2026. This supplied proof is new agent work and must use `misc` if integrated, preserving the source conjecture's history and actual formalization status.

**Sharper choice instance from the independent audit:** RC_(σt,σ) already suffices. A selected point in a missed cell can be added by an admitted operation whose formula guards both uniqueness and compatibility at every world. Full argument: [rc-guarded-progressive-operation.md](/tmp/classicism-research/rc-guarded-progressive-operation.md). This is an operation constructed for this particular progression, not a representation of an arbitrary selected graph. The original stronger-instance proof remains valid.

## 2. Further completeness bridges

The same fixed-point proof establishes, locally at a relational type τ,

* RC_(τ,τ) + represented chain completeness ⇒ BC_τ.
* Internally well-ordered-chain completeness suffices instead.
* Directed completeness is already equivalent to BC in bare C: take the represented closure of an arbitrary family under finite joins.

Details: [quotient-abstraction-lane.md](/tmp/classicism-research/quotient-abstraction-lane.md), §§14–15; the main standalone proof also records the first two refinements.

**New countable bridge:** RC_(τ,τ)+CBC_(κ,τ)+CCC_(κ,τ)⇒BC_τ. Build all progressive f-chains before assuming any completeness. Their union A has pairwise disjoint nonzero increments f(a)∧¬a; CCC makes A internally κ-countable. CBC supplies the one needed supremum and the fixed-point argument finishes. No arithmetic well-order, ND, BF, or operation representation is used.

Full proof: [relational-choice-countable-completeness-ccc.md](/tmp/classicism-research/relational-choice-countable-completeness-ccc.md). Independent quotient-lane and homogeneity-lane audits both passed. The local countable chain condition matches the infinity lane's definition, not a claim that every type is ccc.

Combining the same disjoint-increment argument directly with the audit's guarded progression sharpens the transversal corollary to RC_(σt,σ)+CBC_(κ,σt)+CCC_(κ,σt)⇒TC_σ. The BC upgrade at an arbitrary τ still uses RC_(τ,τ). Thus, under the displayed weaker point-choice instance and CBC, failure of TC_σ would give a represented noncountable disjoint nonbottom family at σt.

**Countable complete Boolean types are internally finite:** C+Ctbl_(κ,τ)(top_(τt))+CBC_(κ,τ)⇒Fin_τ(top_(τt)), for every relational τ. No Choice or infinity premise is needed. In the infinite-index case, the countable enumeration canonically splits an infinite principal ideal into an infinite retained side and a nonzero discarded side. Graph recursion produces disjoint nonzero increments. CBC represents every admitted subset of these increments, and diagonalizing against the enumeration gives a contradiction. In the finite-index case, the infinity lane's §§27–28 make every countable property finite directly. This is internal Frege finiteness, not external finiteness. Full proof: [quotient-abstraction-lane.md](/tmp/classicism-research/quotient-abstraction-lane.md), §21; quotient-lane and extension-lane audits both passed.

Under the given countability premise, CBC is therefore equivalent to internal finiteness. Internal finiteness implies full BC at that type and Actuality in C. The separate equivalence Fin(B_τ) iff Ctbl_κ(B_τ)+CBC_(κ,τ) retains I_κ: a finite numerical index may have too few labels even for a finite Boolean type.

**Finite-index CCC needs no completeness:** C+¬I_κ+CCC_(κ,τ)⇒Fin(B_τ), hence Actuality. The finite-bound lemma says a Boolean ideal whose disjoint nonzero families all fit in a fixed internally finite label set must be finite. Split a non-atomic element into two disjoint pieces; adjoining the opposite piece to an antichain removes one available label, and induction handles both resulting ideals. Explicit graph relabeling avoids hidden operation representation. Full proof and independent extension-lane audit: [finite-index-countable-chain-condition.md](/tmp/classicism-research/finite-index-countable-chain-condition.md).

## 3. Natural language extensions and precise boundaries

[quotient-abstraction-lane.md](/tmp/classicism-research/quotient-abstraction-lane.md), §§7–12, gives the representation and bounded-resource results: arbitrary set-indexed, parameterized pointwise conjunction/disjunction with lambda closure supplies Actuality and Atomicity; C5 upgrades to the full S5 representation. For every fixed regular κ, a <κ-support construction shows bounded infinitary closure plus C5 need not give Actuality/Atomicity. Algebraic BC joins must not be identified with pointwise infinitary operations.

One infinitary numeral predicate standardizing Frege finiteness already obstructs original Maximalism through arithmetic determinacy. This concerns an explicitly enlarged language/resource, with original C retained in Maximalism's consistency side condition.

[homogeneity-amalgamation-lane.md](/tmp/classicism-research/homogeneity-amalgamation-lane.md), §§14–16,24–26, supplies a separate definability boundary in full S5 models with worlds 2^N and only coordinate proposition parameters. Countable well-founded syntax has an atom-selector term in V=L (translate a projective constructible well-order), but no real-coded countable selector term in the stated Cohen extension. Fullness is relative to each ambient universe, and both models satisfy □Functional Choice. The positive translation and negative forcing argument have been internally audited; this is relative independence of the specified definability question, not of □Functional Choice itself.

The same report gives exact profile amalgamation: once full profile conjunctions are admitted, all pure definitions from two parameter blocks preserve joint possibility exactly when the realized joint profile set is the product of the two separate realized-profile sets. Finite-pattern independence alone is insufficient for countable definitions.

**Naming choice resources changes the purity question:** [world-indexed-choice-gallin.md](/tmp/classicism-research/world-indexed-choice-gallin.md), §7, separates the existential equivalence from expanded-language NPC. Naming an event-indexed selector as logical and extending NPC to that language collapses contingency: applying it to top and the property of being an atom names a pure atom. In contrast, all atom-indexed selectors can be named in a full two-world S5 hierarchy while preserving a transitive C2 symmetry, so enlarged NPC and contingency coexist. The homogeneity lane independently checked the all-type construction and modal argument. [check-named-atom-selector.py](/tmp/classicism-research/check-named-atom-selector.py) supplies a small exhaustive output-t check.

Section 8 gives the exact full-model symmetry criterion: for a faithful group action and an invariant family of nonzero event inputs, equivariant selector operations exist precisely when the action on that family is free (with metatheoretic choice for the construction). Zero inputs are harmless; top obstructs every nontrivial faithful symmetry. Full C_p models for prime p can name selectors for all proper events and retain NPC. These countermodels also support arbitrary well-founded set-indexed pure conjunctions. Named atom selectors remove all world stabilizers; a regular group used in their construction is exactly the residual automorphism group.

Section 9 classifies the finite singleton-individual case exactly: a named output-t selector for all nonzero proper events compatible with enlarged NPC exists iff the number of worlds is one or prime. Finite complete type-table formulas define automorphism orbits, so NPC forces transitivity; the selector law then rules out every proper cycle of a nonidentity automorphism. The prime cyclic construction supplies the converse. This is a semantic existence classification, not a claim about every selector or arbitrary Henkin models; its independent homogeneity-lane audit passed.

Sections 10–11 sharpen the scope. Under T, the finite classification applies to ANY model with finitely many proposition atoms, without separate fullness or singleton-individual assumptions; each prime-atom T-model admits a suitable expansion. For arbitrary set-sized FULL S5 models, arbitrary well-founded set-indexed conjunctions/disjunctions plus infinitary lambda bodies yield the same one-or-finite-prime classification, with any individual domain. Named atom choice recursively enumerates propositions up to Hartogs, allowing a pure orbit formula with only finite quantifier blocks. This requires unrestricted set-sized syntax, not merely countable conjunction or a fixed bounded arity. Both the extension and homogeneity audits passed.

The atom-only version has a positive exact description in the same infinitary full-model setting: enlarged NPC is equivalent to a regular effective world-automorphism action, and every set-sized abstract group can occur exactly as that effective group. Individual permutations may remain in the full group's kernel. This final corollary is in §11.4 and has an independent homogeneity-lane audit.

## 4. Other structural results

* [world-indexed-choice-gallin.md](/tmp/classicism-research/world-indexed-choice-gallin.md): over C, □Functional Choice is equivalent to □Actuality plus the precisely defined world/event-indexed witness selector; □Plenitude similarly uses unique-witness description. Individual outputs are handled by relation/haecceity codes.
* [relational-universality-root.md](/tmp/classicism-research/relational-universality-root.md): under the stated T/representation assumptions, universal variation of an individual-indexed proposition family corresponds to a world-to-rigid-profile surjection. Adding profile separation yields exactly one world atom per profile. The attempted analogue with a relational argument type is blocked by a Cantor diagonal, because relational types already contain proposition codes.
* [retraction-extension-lane.md](/tmp/classicism-research/retraction-extension-lane.md): Boolean homomorphism extension, retractions, complete-extension fibre criteria, free complete Boolean algebra characterization of exact profile coding, and Boolean gluing. Distinguish functional graphs (available under RC+BC) from representing operations (still require Plenitude).
* [quotient-abstraction-lane.md](/tmp/classicism-research/quotient-abstraction-lane.md), §§1–6,16,18–19: Actuality is operation-valued extensional canonicalization; TC supplies only a parameterized relational extensional core. At any one relational type, Actuality is equivalent to the actual-null ideal having an algebraically greatest member. Internally finite coextension fibres consequently force Actuality. Under CBC_(κ,t), Actuality is also equivalent to any one actual-null ideal having an admitted κ-countable algebraically cofinal family. No infinity or Relational Choice premise is needed: finite-history graph recursion and an even/odd split of Boolean increments handle I_κ, while the infinity lane's finite-index theorem handles ¬I_κ by a finite null join. The extension-lane independent audit passed. The cofinal-size transfer between null ideals uses existential projection and constant lifting.
* [relative-maximality-boundary.md](/tmp/classicism-research/relative-maximality-boundary.md): rebasing a possibility-maximalization on a pure-incomplete theory satisfying No Pure Contingency makes it inconsistent. This is explicitly distinct from original Max(C).

## 5. What remains unresolved

Relational Choice alone ⇒ Transversal Choice remains unresolved. The finite-cell case is proved; so is the case where all infinite cells have an admitted finite or suitably well-ordered member cover. A counterexample must evade canonical weakly rigid representatives and the full symmetric-Henkin no-go theorem already recorded in the repository.

One source caveat: the existing [relational-choice-r-implies-transversal-choice-r.md](/Users/danielkodsi/Downloads/classicism-map/topics/classicism/writeups/relational-choice-r-implies-transversal-choice-r.md) says all recorded Relational-Choice models realize every actual extension by a *rigid* entity. That adjective is too strong. The proved-only engine and the owning `finite-support-permutations`/`finite-support-one-object` records give Relational Choice and failure of Actuality; rigid realization at every type would give Rigid Comprehension and hence Actuality. The group correctly establishes **extensional fullness** by codomain-dependent profiles, without claiming those profiles rigid. This does not affect its Transversal-Choice argument or the separate symmetric-Henkin no-go proof. No source file was changed.

Simple torsor countermodel proposals failed concrete tests: an equivalence that turns into equality at all future points admits a definable event guard that canonicalizes its rows, and finite-support selectors with only finitely many default classes fail on finite excluded-class covers. Infinitely many named defaults evade the latter immediate obstruction, but no all-type C/Relational-Choice model has been constructed.

The adjacent RC+BC⇒Actuality question is not settled by the new transversal theorem. Completeness gives a supremum of the actual-null ideal but does not by itself keep that supremum null. The proved countable-cofinality criterion above identifies one sufficient extra condition, and BC at tt plus ND at t is another direct sufficient condition; no claim that either follows from RC+BC is made.

The Tame Rigidity + Rigid Power question remains with the dedicated rigidity lane. Our homogeneity report isolates the missing scoped future condition and proves that a free root cannot hide a successor's Tame-Rigidity failure; it supplies no claimed settlement.

## Delivery conventions

Use files, concise chat messages, and low RAM. The user permits natural logical-language extensions and scratch files, but such extensions are labeled rather than silently added to C. Preserve original conjecture/source attribution, human proofs, certificate dates, and Lean status. The latest validation passed: 132 principles, 447 results, 162 models. The finite named-selector check also passed all 512 atom-law and 1,024 equivariance cases.
