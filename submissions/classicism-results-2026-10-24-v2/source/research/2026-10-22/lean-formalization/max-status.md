# Maximalism and Atomicity formalization

**READY FOR INTEGRATION — three source modules frozen.** Ownership of the files below passes to the existing core Lean task for serial compilation, diagnostics, repair, and axiom inspection. The author has not run Lean or Lake. Source preparation and repository validation are not compilation or C certification.

The full Max(C) + unboxed Atomicity_t inconsistency remains **proposed and not formally certified**. No inhabitant of `AtomicitySeparator` has been constructed. No generated statement, YAML status, existing proof, frozen research note, or original follow-up argument was changed.

## Handoff manifest

All three files are under `topics/classicism/lean/Classicism/Results/Research/`.

| File | SHA-256 at transfer | Claim class |
| --- | --- | --- |
| `MaxAtomicitySyntax.lean` | `531f3acdbafd1e6d58476ffa2f4df93325774122c04240943b88e4c7abb121f5` | Actual finite pure object-language terms for Crisp, Small, crisp membership, extensionality, well-foundedness, Fill and Cover; syntactic closed-type/purity proofs |
| `MaxAtomicitySetSyntax.lean` | `339fe71ed4ea99b05054a354ea63f51fb8b3ba38364b903659ae37ceea24ffeb` | Metalogical compiler from finite first-order membership formulas to fixed-type C terms; closed-type preservation and pure binary-predicate abstraction |
| `MaxAtomicityReduction.lean` | `57343a60a522eea406621bbfeaa7897b88716c115de0bd18d05bde6764a1165e` | **Conditional** composition of object-language derivations: a non-theorem identity forced by unboxed Atomicity_t yields inconsistency with pure Max(C) |

Exact commands for the **sole build owner**, from the bundle root, one at a time:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.MaxAtomicitySyntax --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.MaxAtomicitySetSyntax --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.MaxAtomicityReduction --timeout 180
```

The files include `#print axioms` commands for their public conclusions. Inspect those reports and the compiler exit status. If the helper reports an unavailable dependency, follow the core task's established dependency policy; this author has not fetched or installed anything.

These modules live in the metalogical layer. They do not use a shallow proof in Lean `Prop` as a purported C proof. The syntax terms are intrinsically typed `Term Signature.pure ...`; `closedTypes` rules out the metalanguage's extra type variables. The conditional reduction's premises and its contradictory conclusion are `Derivable`/`Theorem` certificates for the exact object language. Thus a shallow gate audit is not the check on these metalogical induction proofs. Any future shallow theorem used to discharge their object-level hypotheses still requires the ordinary gate, type audit, and translated C certificate.

## What is supplied

`coverCode` is the lambda closure of precisely the weakened Cover predicate in the research audit §2. All object-variable types are fixed: t, U=tt, Ut, UUt. Small's injection witness ranges over all proposition-valued functions; it is not incorrectly restricted to crisp subset predicates. Every membership application is explicitly left nested. The additional small-row clause of the earlier HCode is deliberately absent.

`SetFormula n` is an inductive datatype of **finite** first-order formulas with equality and membership. Its binder case lifts the variable environment and the membership parameter; `translate_closedTypes` proves that the translation keeps the paper's type discipline. `quoteBinary φ` binds E,c,G and has a proof of purity and closed types. **No concrete full JSCode formula has yet been supplied.** In particular this generic compiler does not establish that the forcing recipe, regular-open completion, or selector has been implemented or interpreted correctly.

`maximalist_has_nonidentity` uses the official Distinctness form, with non-theoremhood relative to C itself. `inconsistent_of_forced_identity` derives an actual object-language contradiction from the positive identity under the proposed extra axioms and its Max disequality. `atomicityT_inconsistent_of_separator` specializes this to the exact unboxed `P.AtomicityT.schema`. The `AtomicitySeparator` structure is only a transparent list of required proofs; its existence is neither assumed nor asserted. A successful build of this reduction must not be reported as certification of Max + Atomicity inconsistency.

The bounded splitter lemma is owned by `BoundedSplitter.lean`'s author/integration owner. These files neither duplicate it nor rely on its current draft. After it passes its gate, type, and object-derivation checks, its certificate can discharge the positive-identity side for an actual constructed closed selector term.

## Exact outstanding obligations

1. **Concrete finite syntax.** Construct `JSCode_A : SetFormula 2` from the audit's acyclic definitions: finite set coding, standard omega, finite arithmetic graphs, the uniquely indexed master tree, the growth condition, P, regular-open completion, operation graphs, and the numbered coordinate family. Then construct the exact typed Iso, first-split selector, F_A, and S_A. Prove their closed types and purity and check variable capture. The present compiler alone is not this construction.
2. **Full Boolean-valued semantics for this C calculus.** Interpret every admitted type by full functions over a nontrivial complete Boolean algebra, with crisp literal equality and meet/join quantifiers. Prove renaming, substitution, beta/eta/delta conversion and context-hole congruence. Prove soundness of the project's `Derivable`, including **Subst with its logical-axiom side conditions**. Its `H`/Subst presentation is not replaced by an assumed equivalence with a different proof system. The existing `Prop` interpretation cannot witness the needed non-theorem. No such Boolean-valued soundness theorem was imported or postulated here.
3. **Universe coding.** In that full interpretation, prove the semantic equivalence of Small with the cardinal bound, the crisp guards, the Mostowski collapse and small-subset closure, existence of the Cover code, and inclusion of H_(κ+) in every collapse. Prove the relevant cardinalities and the presence of every individual subset of P. Do not silently require P(P) to be an element of the coded universe.
4. **Rigid algebra and splitting family.** Formalize the particular parameter-free Jech–Shelah forcing and its rigid complete atomless completion, or use an independently available checked theorem with exactly those hypotheses. Verify the coordinate family partitions, the zero branch meets, and the least splitting coordinate. There is currently **no Lean axiom for Jech–Shelah** and no proof of this construction in these modules. This is a substantial library/proof dependency, not an omitted one-line lemma.
5. **Presentation independence and term value.** Prove absoluteness of the concrete set formulas for every permitted collapse; rigidity gives uniqueness of the isomorphism after collapse. Establish crispness and unique q for the actual typed selector, then that the existential assembling F_A has value q and S_A has value top. Combine with the full soundness theorem to construct `not_zero_theorem`.
6. **Exact C connection.** Use the separately certified bounded-splitter derivation, with b=top, and verified quotation/conversion steps to supply `zero_under_atomicity` for that same S_A. Only after both fields are proved can the conditional reduction yield the requested full result. The countable Henkin extraction in audit §10 is an optional additional model formalization, not a substitute for these missing certificates.

## Scope and validation

Direct source: [finite selector audit](../followup/max-atomicity-selector-audit.md), especially §§2–9. All new formal work is attributed to this research formalization, not to the imported paper's authors. The underlying proposed mathematics remains subject to independent scrutiny.

The later permission to use natural language extensions is not exercised: all three modules retain the original finitary pure relational C language. There is no infinitary conjunction, type quantifier, selector constant, added mathematical axiom, or `sorry`.

Repository validation after the source/status batch: `python3 scripts/pmap.py validate`; compact log at `.reproduction/classicism-max-formalization-validation.log`. Last verified count: 132 principles, 447 results, 162 models — OK. This checks the bundle, not Lean elaboration or the proposed theorem.

## Subsequent verification request on 22 October 2026

The three original modules now match successful source/dependency-fingerprinted checks. The bounded-splitter module also has a matching successful check. The full inconsistency remains without an unconditional Lean certificate.

Two fresh modules are **READY FOR INTEGRATION** and frozen: MaxAtomicityHCodeSyntax and MaxAtomicitySplitCertificate. The latter derives the exact split zero identity for arbitrary closed F from the actual unboxed Atomicity schema, instead of requiring that derivation as an input. Its final inconsistency theorem still requires the non-theorem certificate.

See [the precise status](max-lean-verification-status.md) and [hashes and serial commands](max-verification-handoff.json). The designated compiler has resumed; this author ran no Lean/Lake process and takes no ownership of previously transferred files.
