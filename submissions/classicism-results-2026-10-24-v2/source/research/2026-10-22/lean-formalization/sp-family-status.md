# SP, Max, effective metatheory, and infinitary-boundary coverage

22 October 2026 (user's time zone). This is a continuation of the full assigned
scope, not a reduced shortlist. The original notes and coverage registry are
unchanged. Every currently assigned queue key is retained in
`sp-family-inventory.json`, with the original source entry and exact remaining
obligation. No family is removed because its dependency is large.

## Evidence levels

Updated 23 October: the [verification ledger](sp-verification/verification-status.md)
records all twelve submitted result modules as passing against their current
sources and dependencies: C, Stability, Schemas, MaxDiagram, Algebra,
Computability, InfinitaryNumerals, Reflection, UniversalCore, Disjunction,
SignatureSplit and MaxConservativity. An additional CoreAxioms module passes
21 public declaration and axiom audits for the last two. C and Stability supply
31+8 gate/type/object-derivation certificates. The author verified four modules;
the core task repaired Schemas, Reflection, SignatureSplit and MaxConservativity;
the dedicated proof agent repaired UniversalCore and Disjunction. Algebra,
Computability and InfinitaryNumerals are ordinary metatheory, not C certificates.

All twelve source-module checks are complete. A checked supporting lemma or
conditional criterion does not verify a broader main-family claim. The exact
remaining mathematical and implementation obligations below are retained.
Historical handoff hashes are in `sp-status.md`; current accepted hashes and
logs are in the ledger. The user's explicit verification request superseded
the earlier source freeze for these authorized repairs. No family below is
declared complete merely because a supporting module compiles.

The significant new implementations are: the exact Max identity diagram and
relative-distinctness stabilization; the converse equational-conservativity
test; two actual singleton signature models and the two-instance atom split;
finite-proof Max reflection and the conditional exact SP BoxNe diagram; a
structural universal-identity grammar proof and its exact SP schema equivalence;
the restricted disjunction criterion; actual self-referential program proofs;
and explicit enlarged infinitary syntax with its local numeral-exhaustion proof.

## Shared obligations, stated precisely

**M1 — Genuine complete-model construction.** The existing library supplies
typed action/intensional models and soundness. The targeted search did not
locate a theorem producing a genuine action/Henkin model from every consistent
C theory. Implement the completeness/term-model construction, including full
quantifier interpretation and witness closure. This is needed for the component
family in the profile/coalescence proofs; it cannot be replaced by a Boolean
quotient with no higher-type witnesses.

**M2 — Pure profile root and finite pointed completeness.** Implement the actual
one-individual root, pure unary term-profile quotient, arbitrary current
extension coordinate, transport/application/abstraction closure and soundness;
prove pure Max and simultaneous Atom(F and E_n) at that root. Prove finite full
extensional uniqueness and individual transitivity, with entity equality at all
descendants rather than only present truth. These are completed ordinary
research arguments, not new open consistency questions. The root is explicitly
not an SP model. The new SignatureSplit module discharges only the other side:
the two full finite signature consistency witnesses and signature Max's split.

**A1 — The actual C arithmetic interpretation.** Connect the existing quoted
N, zero, successor, Sum, Prod and I_sigma to genuine models; prove the required
PA/relativized finite-run facts, numerical injectivity of full-term maps and
the stated standard-numeral recursion facts. A set-theoretic map satisfying
those hypotheses is not a substitute for this bridge. Preserve the original
source-access caveat in infinitary-standard-numerals-20261022.md §1.

**E1 — Effective syntax and finite proofs.** Supply recursive encodings of the
fixed relational types, pure terms/sentences, substitution/conversion witnesses,
and actual finite C derivations. Prove the proof-checking predicate has exactly
the claimed recursive/relative complexity. The derivation inductive datatype
and finite-support theorem alone do not provide these computability proofs.

**E2 — Effective adequate models and completions.** Specify the exact numbered
many-sorted domains, equality, total application, term interpreter, and actual
valuation; build relative-effective fresh-Henkin witnesses and a quotient with
decidable equality. Prove both reductions and exact-degree preservation, while
keeping old pure Max's schema fixed under added witness names. Bare application/
equality codes must remain distinct from adequate codes.

**E3 — Relativized recursion and basis theory.** The available Mathlib source
has actual partial-recursive codes, a recursion theorem, recursive-in-oracle
relations and Turing-degree basics. The targeted Computability/ModelTheory
search did not locate the needed Low Basis, cone-avoidance or HYP/Kleene-O basis
theorems. Implement/import exact checked statements with uniform oracle-index
compilers, not an unspecified jump oracle. The new computability module proves
the unrelativized diagonal-program core; it does not close these obligations.

**E4 — Effective spaces and standard semantics.** Define the fixed sentence-bit
Cantor coding, completion loci, effective Borel hierarchy, recursive trees and
standard-number model-code class. Prove the topology/complexity reductions and
the claimed basis/cone arguments. A model capacity bound is not a spectrum of
one structure, and a lower bound is not a theoremhood classification.

**I1 — Infinitary interpretation bridge.** The new numeral fragment defines
external countable disjunction inside open formulas and a lambda beta law,
then derives the standard range from impredicative numberhood. To finish
principles.24, interpret this fragment at every relevant world of the original
typed model, prove Sum/Prod standardness, and supply the two old-C independent
arithmetic branches. The old Max reference remains finitary C. An external
Boolean description of old sentences supplies no open-formula comprehension.

## Exact per-family remaining list

The queue IDs below are the coverage audit's IDs; references and qualifications
are retained verbatim in the companion JSON. Module names omit the common
`StrongPossibilityConsequences` prefix.

| Queue key | Implemented portion, not yet a full-family verification | Exact remaining main obligation |
| --- | --- | --- |
| principles.03 | Existing arithmetic syntax only | A1 and the converse model realization proving the exact common first-order arithmetic theory of the specified positive packages and Choice additions. |
| principles.04 | MaxDiagram supports the identity fragment only | A1, M1/M2, and both arithmetic-theory inclusions for Cn(T+TruePi1), retaining the specified graph-choice package. |
| principles.12 | SignatureSplit constructs both relational-constant witnesses | M2; the empty/one-individual-name preservation proofs; the two-individual-name obstruction; exact finite-signature classification. |
| principles.13 | Existing finitary proof support can be reused | Formal signature renaming/substitution with an infinite type-correct fresh-name reservoir; conservativity of the stated theory, not merely C. |
| principles.14 | MaxDiagram gives the exact finite Boolean identity fragment | E1 and the actual computable Sigma1-hardness reduction to pure C identities; M1/M2 for unconditional Max existence. |
| principles.15 | MaxConservativity implements both logical directions with Con(Max) | E1, E2 and the two oracle-cone reductions; effective hidden-variable interpretation obstruction. |
| principles.16 | Computability gives concrete unrelativized diagonal programs | A1, E1, E3: definable correct halting bits, uniform oracle recursion/inseparability for every consistent 0'-c.e. strengthening, and matching upper bound. |
| principles.17 | No actual adequate-code/degree implementation yet | E2/E3: both PA-over-0' capacity reductions, uniform DNR equivalence, relative-low models, common information and no least solution degree. |
| principles.18 | Computability supplies the base diagonal obstruction | Explicit C finite trace compiler under possible weak Infinity; A1/E1/E2/E3; bare-code nonbottom extraction without assuming Actuality/valuation. |
| principles.19 | No HYP/basis implementation yet | A1/E2/E3/E4: full standard arithmetic comprehension, fixed-point obstruction, sub-O basis construction and exact common information; retain standard-model existence for each theory. |
| principles.20 | MaxDiagram supplies only the fixed identity-fragment distinction | E2/E4: actual recursive-tree graph realization and both analytic reductions for standard B/F and Max, with the different identity-fragment bounds. |
| principles.21 | No effective finite-bound/structure implementation yet | Finite-trace obstruction plus effective extraction of exact/necessary sort sizes, actual typed-structure uniqueness, computable Henkin copy and pointed-transitivity criterion. |
| principles.22 | No completion-space implementation yet | E2/E3/E4: nowhere density, positive isolated completions/perfect derivative, dense low solutions and exact effective-Borel assertions, each in the fixed coding. |
| principles.23 | MaxDiagram proves stabilization; MaxConservativity proves the converse test with Con(Max) | Compiler acceptance and M1/M2 to discharge Con(Max) in an unconditional library corollary. Recomputed distinctness is not the optional hat hierarchy. |
| principles.24 | InfinitaryNumerals explicitly defines enlarged syntax and proves local exhaustion/unique names | I1; global accessible-world nonstandardness forced by old Max and the incompatibility conclusion. No finitary inconsistency is claimed. |
| principles.25 | Reflection proves finite-support persistence and exact conditional BoxNe diagrams | A1/E1/E2/E3: full Sigma3-completeness and PA-over-0'' reductions, retaining Con(SP); no standard-SP existence inferred. |
| principles.27 | SignatureSplit gives signature Max's pure-cell refutation; UniversalCore gives reflection | M1/M2, unconditional pure-SP atom theorem, joint incompatibility, arrow iff antecedent inconsistency, and exact finite individual-name bounds. |
| principles.29 | Atom reflection/splitting C certificates only | Pure/profile and finite-signature atom laws, exact all-input-type BF/Functionality failure terms and all stated finite-signature hypotheses. |
| principles.30 | Max finite-proof reflection mechanism available | Define optional finite hat stages; full modal induction, arithmetic jump compilers and relative PA capacity/strictness, each conditional on the specified stage consistency. |
| principles.31 | Existing finiteStage/theorem_at_stage supplies the finitary union mechanism | Actual self-consistent uniform compiler, least-closure omega-jump predicate, exact omega-stage capacity/theoremhood and absolute Pi2 completion description. Preserve all-stage consistency. |
| sp_supplement.01 | UniversalCore and Disjunction implement syntactic core/equivalence and restricted disjunction criterion | Compile exact statements; normalized H-disjunction version, H-clopen embedding invariance and the genuine-model elementary-extension embedding criterion. No joint-embedding theorem is supplied. |
| sp_supplement.02 | Algebra has conditional modal-ideal calculations | Full operation-signature essentiality/density equivalence and sufficiency for genuine SP models; failures of Vicinity/Actuality. Necessity of essentiality remains unproved. |
| sp_supplement.03 | Algebra proves a specified quotient excludes new fixed points | Actual maximal B-preserving quotient, Zorn/essentiality proof, finite polynomial-chain survival criterion, correct-truth ultrafilter and genuine Henkin completion; no SP model conclusion. |
| sp_supplement.04 | No guarded interpolation implementation yet | Actual finite old-term witness/interpolant construction for each stated guard and finite table, including forbidden-function avoidance; no unrestricted incoming higher operators. |
| sp_supplement.05 | No product/ultraproduct implementation yet | Typed full-term product embeddings, finite-intersection pair-separation family, ultrafilter construction and injective quotient; finite-product injective coordinate corollary. |
| sp_supplement.07 | C atom/split lemmas only | Actual SP strong-world exclusion at every relational type and the stated possibilities preserving finite current diagrams; do not refute weak atoms or unboxed Actuality. |
| sp_supplement.08 | No closed-pure persistent-ghost construction yet | Explicit pure persistent operators, Max nonzeroness, SP bottom entity-values, finite coextensive multiplicity and the contrasting single-individual-input theorem. |
| model_interpretation.04 | Semantic representation infrastructure belongs to the model lane | E2 and exact degree-preserving effective Gallin reconstructions in both directions; preserve truth and signature qualifications. |
| model_interpretation.05 | No exact-degree model construction yet | E2/E3: uniformly construct a model of precisely the supplied complete pure theory and its exact degree; prove full-space parametrization needs the stronger oracle. |
| F13 | Algebra proves only restricted Boolean/map kernels | Truth-preserving Boolean absorption/elementarity for arbitrary finite alternations and fixed evaluations, plus guarded numerical witnesses; actual full C algebra bridge. |
| F14 | Reflection supplies Max/SP BoxNe diagram, not arithmetic correctness | A1, one-step C+I omega-rule, true Pi02 consequences, conditional sharp boundary and the explicit numerical H-Barcan obstruction. |
| F15 | Algebra supplies conditional numerical-retraction/quotient lemmas | A1 numerical preservation/injectivity from genuine full-term maps; M1 for local embedding iff D; actual target-kernel characterization and generic profile canonicity/no-go. Henkin completion for the desired SP model remains unresolved. |

## Scope cautions

SP consistency and its higher-stage analogues remain genuinely open here. The
pure-profile model, ordinary Max consistency, finite signature witnesses and
effective metatheorems in the source notes are instead implementation work;
they must not be mislabeled open mathematics merely because their Lean proofs
are missing. Con(Max) parameters in current files expose that library gap.

All degree/classification families remain open in this formalization inventory
until their actual reductions, codes and matching bounds are checked. The
unrelativized recursion-theorem lemma alone does not prove Sigma2/Sigma3
completeness, PA capacity, a Low Basis theorem or a standard model.
