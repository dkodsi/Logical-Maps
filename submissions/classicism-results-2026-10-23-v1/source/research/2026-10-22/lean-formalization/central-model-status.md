# Central negative model: author handoff

22 October 2026. The seven modules in `central-model-manifest.json` have recorded source hashes; a successful check is required for certification.

## Concrete first witness

The first target uses the permitted signature Sigma={c:et}. The coordinate
set is P(Nat), the free-monoid alphabet is the type of pure finitary formulas
with one free et variable, and the individual domain is a singleton. The
typed domains are recursively constructed countably supported intensions.
The whole product is used for arrows; their supports are unrestricted.

The drafted exact package is Logical Necessity, all-type boxed Barcan, and
all-type boxed Relational Choice, with failure of Actuality. The top theorem
`Central.OneConstant.package_not_entails_actuality` uses the existing
`AxiomSet.logicalNecessity`, `P.NecBarcan.schemaIn`,
`P.NecRelationalChoice.schemaIn`, `P.Actuality.schemaIn`, and intensional C
soundness. It does not assume an abstract countermodel or an existence bridge.
The companion theorem states consistency of that package.

This is the finite-signature first witness requested by the coordinator.
The larger signature-uniform and completeness packages are not claimed here.
All claims in this handoff describe the intended statements of saved drafts,
pending successful integration.

## Dependency order and substance

1. `CentralSupport`: externally controlled supports, actual mutually recursive
   domains, injective/natural inclusion, term-closure proof, `model_isModel`.
2. `CentralSupportedProduct`: countable coordinate controls; equivalence of
   whole-entity support and profile dependence; arbitrary constant extension
   profiles; existential suffix lift; onto maps at every type; exact boxed BF.
3. `CentralSupportedProductNegative`: Cantor diagonal fresh coordinate;
   coordinate truths and their permanently killing arrows; no least actual
   truth; failure of the library's exact quoted Actuality sentence.
4. `CentralSupportedProductGluing`: common predecessor of a countable family
   of entire relations at any fixed relational type. Equality includes all
   future arrows and all argument tuples, not just actual extensions.
5. `CentralSyntaxCountable`: mutual type encodings, raw finitary syntax
   retaining hidden application types, and injection/countability of terms.
6. `CentralLogicalNecessity`: choose one semantic witness for each satisfiable
   pure unary formula, glue them into c, verify unary and empty constant-tuple
   instances, exhaust every distinct tuple in the single-constant signature,
   and use soundness for Actuality nonderivability.
7. `CentralSupportedProductChoice`: extension fullness via arbitrary constant
   profiles; reuse `FullModels.holds_box_rc`; combine the exact schema package
   and its Actuality nonentailment. Current Transversal Choice is also obtained
   from the existing extensionally-full theorem.

The ordinary source is `followup/central-map.md`, §§1–3 and 6 (`misc` for any
future record). The source's published pinning background is not credited
with these new proofs. All preexisting modules, research proofs, YAML records,
and generated Statements.lean were preserved.

## Checking

Run only through the certificate checker's serial workflow, in the manifest
order. Check `Classicism.Semantics.Research.CentralSupportedProductChoice`
after its dependencies and inspect the axioms of `B_isModel`,
`holds_logicalNecessity`, `holds_package`, `package_not_entails_actuality`,
and `package_consistent`. No mathematical axioms or proof placeholders were
added. The syntactic injection proof uses ordinary dependent induction and
`aesop`; it is an elaboration checkpoint, not an assumed countability axiom.

Other likely integration checkpoints are recursive type reduction in the
argument isomorphisms, equality casts in extension fullness, and the exact
quoted Actuality simplification. Source-level mathematical inspection is not
represented as a successful compiler result.

Repository validation after the author batches passed:
`132 principles, 447 results, 162 models — OK`.

## Remaining substantive obligations

- Compile and repair the first concrete certificate above.
- Prove the supported model's exact boxed Tame Rigidity verdict through the
  coordinate factorization and exact-image characterization.
- Connect external countable joins to the map's internal Countable BC using
  the actual finite-cardinality successor orbit; cardinality of external
  domains alone would not establish it.
- Add the exact quoted Vicinity bridge; its stronger permanent-killing
  witness is already in the draft.
- Construct the separate symmetric model and prove its full BC/WRP package
  and choice obstruction. Its domains do not admit arbitrary constant graphs.
- Generalize signature cardinality and treat the moving-individual infinity
  variants separately.

No one of these remaining claims is certified by the present validator or by
the already written first-witness theorem statement.
