# Infinity, arithmetic, and world richness: consolidated research note

22 October 2026. Ordinary mathematical research in the fixed relational-type framework C. This note consolidates the arguments and cross-checks in the linked scratch reports. Its new results are mathematical arguments developed in this research session, not previously recorded results or a claim of external referee review. It makes no literature-novelty or Lean-verification claim. Original database records and human-authored proofs have not been edited.

## Scope and notation

C is fixed. C5 means C+□ND, not merely current ND. BP means C+□Plenitude, equivalently C5+Atomicity in the recorded theory. F means C+□Functional Choice. Pure Maximalism and Strong Possibility retain their original consistency side conditions and reference theories. No e-valued operation type is added: selections and bijections with individual outputs are relational graphs.

At each counting type σ, νσ=(σt)t and Nσ are the Frege finite cardinalities. Infσ means that the entire σ-domain has no finite cardinality. Iσ is the possible successor-injectivity condition used by the arithmetic interpretation; its exact characterization below does not identify it with Infσ in bare C.

## 1. The central distinction: arithmetic infinity versus domain infinity

New argument: already in bare C,

    Iσ ↔ successor is injective on Nσ
       ↔ ¬Nσ(⊥νσ)
       ↔ every Nσ-cardinality is possibly instantiated
       ↔ Nσ is not Frege-finite.

When infinite, Nσ admits the Dedekind shift n↦Suc(n); otherwise it is Frege-finite. There is no amorphous middle case for this particular numerical domain. Infσ implies Iσ in C. C5 makes the converse valid, using numerical null collapse; bare C does not.

A precise separating model has a singleton root over full one-world components with j individuals, one for every positive external integer j. At the root I_e holds and N_e is standard, but every world has finitely many individuals. Therefore I_e∧¬◇Inf_e is consistent with C. This model also verifies boxed Boolean Completeness, Atomicity, Strong Leibniz, Rigid Comprehension and Relational Choice. Its Barcan distinction is exact: boxed BF holds for every relational quantified type but BF_e fails.

Proofs: [Frege report](frege-infinity-20261022-1726.md), §§26–28 and 33. Earlier §§7 and 25 supply the finite-cardinality lemmas.

## 2. Mathematics is already available; stability is an additional issue

C+Iσ interprets ordinary second-order arithmetic, and more generally finite-order extensional relational arithmetic, by current extensional quotients. Numbers are Nσ; sets are current predicates on Nσ; set equality is current coextension. The higher-order version recursively restricts to predicates invariant under lower-type extensional equivalence. Lambda comprehension and unrestricted Frege induction supply the interpreted comprehension and induction schemas. This interpretation does not identify arbitrary coextensive intensional entities or add a description/choice operation.

C5 supplies a stable hereditary rigid core. Under BP, the current extensional quotient and rigid representatives can be compared canonically using the local Boolean truth evaluator. The evaluator is world-local: asserting one fixed evaluator works necessarily is a substantially stronger collapse principle.

Consequently, a finite primitive individual core under Strong Possibility would not by itself prevent current arithmetic or analysis. The substantive contrasts concern modal stability, rigid representation, collection, and functional choice.

**Exact arithmetic conservativity.** The audited model transfer now shows that, for any counting types σ and ρ, C+Iσ, C+Infρ, C5+Infρ, BP+Infρ and BP+all-type Infinity have the same ordinary first-order arithmetic consequences under their respective Frege interpretations. The proof passes to current extensional quotients and inflates to an internal S5 model whose worlds are its numbers. It preserves nonstandard numerical models as well as standard ones.

A further source-based deduction extends this equality to C+□Functional Choice+Infρ, even to the package with all-type boxed Infinity. For each finite proof, a sufficiently large finite fragment of set theory with Choice builds its full S5 interpretation. McLarty’s number-preserving constructibility interpretation then returns that finite fragment to finite-order arithmetic. The use of this external theorem is explicit: [McLarty, *Interpreting set theory in higher order arithmetic*, §§3–5, pp.3–6](https://arxiv.org/pdf/1207.6357). This is first-order arithmetic conservativity, not higher-order or modal conservativity.

Let T be the common effective arithmetic theory. It also has a familiar description: T is the first-order arithmetic consequence theory of the finitary union Z_<ω of all finite-order extensional arithmetic theories Z_n. Each theorem uses some finite order; no single fixed order is asserted to suffice. The further converse argument gives an **exact characterization**:

    Th_arith(Pure Max(C)) = Cn(T ∪ TrueΠ₁)
                         = Cn(T ∪ TrueΣ₂).

Here TrueΠ₁ and TrueΣ₂ mean standard-true first-order arithmetic sentences of those respective complexities, and Cn is ordinary deductive closure. This concerns actual arithmetic theorems, not truth at every possible state. Pure Maximalism contains T and proves its true Π₁ consistency sentence Con(T), which T cannot prove. Its ordinary arithmetic theory therefore **properly extends** the arithmetic of the positive □Functional Choice package with infinity, while falling short of all arithmetic truth.

The upper-bound proof is worth specifying because the consistency side conditions matter. If A is not in Cn(T∪TrueΠ₁), compactness gives a C+I_e model satisfying all translated true Π₁ sentences and ¬A. The current quotient and McLarty interpretation preserve its numbers in a bounded-powerset set model S. A putative finite Max proof of A requests only finitely many possible C-consistent sentences φ_i. Their true Π₁ assertions Con(C+φ_i) hold in S. The direct typed Henkin construction supplies coded C+φ_i component models inside S. A free current root over these components, with individuals ω^S, satisfies those possibility axioms while retaining precisely S's arithmetic and hence ¬A. Only finitely many type domains and powersets are required, including all types used in the arithmetic-correctness arguments and H certificates licensing Logical Equivalence.

This uses the countable BBK completeness construction in Bacon–Dorr, *Classicism*, **1 July 2022 draft**, §3.1, Theorem 3.2, pp.44–45 and footnote 64; the following paragraph extends it to H-extensions. [Inspected author manuscript](https://andrew-bacon.github.io/papers/Classicism.pdf). These locators deliberately differ from the map's usual 16 May 2023 draft. The exact arithmetic characterization is our deduction from these source results and the displayed model construction; it is not attributed to either source.

The same arithmetic characterization survives adjoining current Relational Choice, Transversal Choice, Well-Ordering, and all-type actual Infinity to Max. Internally full current graph extensions provide these current assertions. This corollary does not add boxed choice, Plenitude, or rigid comprehension.

Finite individuals need not prevent the positive arithmetic interpretation either. For each fixed positive integer m, BP with exactly m individuals and Infinity at all relational types has arithmetic theory T at each **relational** counting type. Its e-counted arithmetic is finite, so that counting-type qualification is essential.

Proofs: [Relational report](relational-coding-recursion-20261022.md), §§24–33 and 36–37; [Frege report](frege-infinity-20261022-1726.md), §§35–37. The BP comparison has a direct model proof independent of McLarty’s theorem. The exact Max characterization and the Functional Choice comparison use the explicitly stated source bridges.

### Canonical arithmetic graphs need not be operations

The simplest obstruction already uses one counting base. For every admitted σ, Pure Max proves

    ¬∃f:νσ→νσ ∀n∈Nσ [f(Sucσ n)=n].

Thus there is no numerical predecessor operation. Nevertheless C+Iσ proves that the ordinary predecessor graph is total and single-valued on numbers, and the graph can be completed by zero off its intended domain. Plenitude supplies an operation representing that graph. These are different claims: first-order arithmetic uses the functional graph, while the displayed formula demands one higher-type entity implementing it.

For the short contradiction, choose a full finite Fregean model and let its σ-domain have standard finite size m. There (m+1)σ=(m+2)σ=bottom but mσ≠(m+1)σ. Max makes that closed pure collision possible. The assumed predecessor operation gives f((m+1)σ)=mσ and f((m+2)σ)=(m+1)σ at the root. Necessary Identity preserves both equations, so at the possible collision their equal inputs would have unequal outputs. No Barcan inference or transport of the universal predecessor assertion is needed.

In C define J_{σ,ρ}(x,y) as the least relation containing (0σ,0ρ) and closed under simultaneous successor. Under Iσ it is a total functional surjection Nσ→Nρ; under Iσ+Iρ it is a current bijection preserving zero, successor, addition and multiplication. This gives agreement of current arithmetic across counting types in the original model, without claiming identity of intensional graphs or an operation representing the graph.

Pure Max makes the distinction particularly sharp. It proves both

    ¬∃f:ν_e→ν_t [f(2_e)=2_t ∧ f(3_e)=3_t],
    ¬∃g:ν_t→ν_e [g(3_t)=3_e ∧ g(4_t)=4_e].

The first obstruction uses a possible Fregean world with one individual: 2_e and 3_e collapse to bottom, while 2_t and 3_t differ. The second uses a possible Fregean world with four individuals: 3_t and 4_t collapse, while 3_e and 4_e differ. Necessary Identity transports the assumed operation values and yields each contradiction. Thus the canonical current bijections exist as graphs but cannot be represented by operations in either direction. Plenitude represents the padded unique-output graphs, so it removes precisely this obstruction.

Proofs: [Relational report](relational-coding-recursion-20261022.md), §§34–35 and 38. Subscripts separated by a comma, such as J_{e,t}, refer to two counting bases; et without that comma is the individual-predicate type.

## 3. Maximalism fails one explicit numerical join

For any proposition q, form H_q={λm.q∧m=n:n∈Nσ} and Q_q=λm.q∧Nσ(m). In C, existence of the Boolean least upper bound of H_q is equivalent to Q_q being that bound, and to the relative collection formula

    ∀X[(∀n∈Nσ □(q→Xn))→□(q→∀n∈Nσ Xn)].

The instance q=Iσ suffices for the arithmetic-necessity argument. Pure Maximalism refutes this particular join. Equivalently, its canonical increasing family of finite numerical initial segments, guarded by Iσ, has no Boolean least upper bound. This is more concrete than an unspecified failure of a completeness schema.

The associated arithmetic phenomenon is precise: Max can prove Con(Tσ), while making Iσ∧¬Con(Tσ) possible, where Tσ is the effective arithmetic shadow of C+Iσ. At an Iσ-world witnessing the latter, a purported proof certificate must exceed every current numerical bound. This is not a contradiction in the actual arithmetic theory, and moving the outer quantifier over current bounds inside the possibility/necessity operator would be invalid.

Proofs: [Frege report](frege-infinity-20261022-1726.md), §§12–18 and 23.

## 4. Exact higher-type infinity and core finiteness

In C, the relevant Functionality instance gives

    Fin(σ→τ) ↔ Fin(σ) ∧ Fin(τ),  τ≠e.

The nontrivial direction bounds existing functions by finite restrictions; it does not assume arbitrary finite interpolation. Hence under BF, a relational type containing e is infinite exactly when e or t is infinite; an e-free relational type is infinite exactly when t is infinite. Full S5 models satisfying □Functional Choice realize all four combinations of finite/infinite e and t.

Separately, in bare C, taking the rigid powerset preserves Frege finiteness and infinitude. Every primitive hereditary core containing e is finite iff e is finite; every e-free primitive core is canonically finite. An infinite mathematical core can instead be based on rigid Nσ under C5+Infσ.

Proofs: [Root audit](infinity-world-richness-audit-20261022.md), §F; [Relational report](relational-coding-recursion-20261022.md), §§24, 27 and 30; [Frege report](frege-infinity-20261022-1726.md), §31.

## 5. World representation: three different assertions

Raw WRσ asks for V:σt such that every current σ-profile is represented by an atom w through Xx↔w≤Vx. Raw UWRσ asks for a unique representing atom. The original UCP instead asks that every rigid profile be possibly realized; AUCP asks that its agreement proposition itself be an atom. Over BP the corresponding forms agree. Outside BP they must be kept separate.

C itself refutes unrestricted WRσ for every relational σ, by a Cantor diagonal. Individuals, and finite tuples consisting solely of individuals, admit full S5 representation models. In full models, worlds P(D) give unique representation of all individual profiles and satisfy □Functional Choice.

Pure Maximalism directly refutes original AUCP_e. Nevertheless new profile-root models satisfy Pure Max+UCP_e+raw UWR_e with any prescribed positive finite individual domain, or with an actually infinite individual domain. They retain an atomless remainder and do not satisfy Atomicity. Thus raw uniqueness does not repair the stronger atomic-agreement claim.

Proofs: [World report](world-cardinality-ucp-20261022.md), §§12–17 and 28–33; [Fresh-profile construction](fresh-constant-profile-root-20261022.md), §§1–11.

## 6. Choice-free calibrations and the limits of world richness

Explicit finite-support S5 Henkin models in ordinary ZFC satisfy BP while failing Functional Choice. One has both individual and propositional infinity, yet its propositions are relationally Dedekind-finite, even in the multivalued convention used by the records. It has no countably independent family of propositions, although its proposition domain surjects onto the numbers.

A second nominal construction satisfies BP+UWR_e+both infinities while still failing Choice. More generally, world representation at every fixed finite rigid-power rank can hold simultaneously without Functional Choice. These are admitted Henkin profile hierarchies; they are not claims that every external subset has a representative.

Under □Functional Choice, by contrast, propositional infinity is equivalent to numerical Boolean independence when indexed by N_t. Under BP, countable independence is equivalent to a surjection from atoms onto the appropriate infinite numerical domain. The index matters: N_e can be finite even when propositions are infinite.

Proofs: [World report](world-cardinality-ucp-20261022.md), §§22–27 and 34–36.

## 7. Pure names cannot name an actual atomic world under Max

For every fixed closed pure proposition term A and counting type σ,

    Max ⊢ Atom(A) → A≤¬Iσ.

If C+A+Iσ were consistent, its effective arithmetic interpretation would yield a sentence splitting it into two consistent extensions. Max makes both pieces possible, refuting atomicity of A. If it is inconsistent, C already proves A≤¬Iσ. This is an instance-by-instance metatheorem, not an algorithm deciding the consistency side condition.

Since Max entails Iσ, no closed pure term can witness Actuality. This does not refute Actuality: the fresh-root constructions have an actual strong atom that lacks a pure closed name. Any Max+Atomicity model needs atoms with no closed pure name below Iσ. A model whose propositions are all denoted by closed pure terms therefore cannot satisfy Max+Atomicity; this does not exclude term presentations using extra constants, and general consistency remains unresolved.

Proof: [Fresh-profile report](fresh-constant-profile-root-20261022.md), §15.

Max also forces an internally infinite region below ¬Actuality. With P=¬Actuality and h(n)=P∧(Suc_e n)(top_e), it proves ∀n∈N_e ◇h(n). The h(n) are pairwise disjoint and nonzero, so the interval below P is relationally Dedekind-infinite. If even local Atomicity below P is added, its atoms admit a surjective relational graph onto N_e. All these atoms are non-strong worlds: each must split at its truth locations. This supplies a concrete necessary condition for any Max+Atomicity model, without resolving its consistency or selecting one atom for each number.

Proof: [Fresh-profile report](fresh-constant-profile-root-20261022.md), §16.

## 8. Boundaries retained

The work does not establish consistency or inconsistency of Strong Possibility, does not classify its ordinary arithmetic theory, and does not settle Pure Max+Atomicity_t. It does not establish whether these formulations are new in the literature. Missing arrows in the local map are not evidence of nonimplication.

The arithmetic end-extension analogy needs care. Full arithmetic end-extension frames can modally define the standard cut and violate modal induction in nonstandard models. C requires induction for all admitted modal predicates. Nonstandard numerical domains nevertheless occur in Henkin models of C, including □Functional Choice and Pure Max models obtained by ultrapowers. The external standard cut is then not an admitted predicate.

All new constructions and arguments remain scratch research, separate from the database.
