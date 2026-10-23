# Lean certificates: pure Maximalism and unboxed Atomicity

**Verified on 23 October 2026.** The exact theorem and all 47 MaxAtomicity background modules have successful Lean checks matching their current recursive local source closures. The final serial run completed with exit code 0, no source drift, and matching current source hashes.

## Exact theorem

```lean
theorem maximalism_atomicity_inconsistent :
    ¬ AxiomSet.Consistent (AxiomSet.maximalist ∪ P.AtomicityT.schema)
```

The full declaration name is `Classicism.Meta.Research.MaxAtomicityInconsistency.maximalism_atomicity_inconsistent`. Its [source](../../../topics/classicism/lean/Classicism/Results/Research/MaxAtomicityInconsistency.lean) has no mathematical input premises. This is the fixed theory C plus the original pure Max(C) schema and unboxed Atomicity at type t.

- [Successful exact-target compiler manifest](checks/20261023T054730505817Z-9a834f08.json).
- [Exact theorem type and complete axiom report](logs/runs/20261023T054730505817Z-9a834f08/Classicism_Results_Research_MaxAtomicityInconsistency.log).
- [Complete certificate package](max-atomicity-lean-certificates.zip).
- [Ordinary mathematical proof and implementation guide](max-atomicity-canonical-code-proof.md).
- [Machine-readable source and axiom audit](max-certificate-audit.json).

The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. Its complete report contains no `sorryAx` or custom mathematical axiom. These are standard external Lean metatheoretic axioms, not additional inference rules or optional principles inside C. All coding, rigidity, generation, atomlessness, soundness, and syntactic obstruction obligations are supplied by proved dependencies.

The proof uses the actual Jech–Shelah rigid atomless complete Boolean algebra, its countable canonical generators, finite hereditary set coding, and a least-natural-index pure selector. The ordinary proof gives the original source attribution and the formal implementation details. No L assumption, CH, enriched signature, infinitary conjunction, or boxed Atomicity is a premise of the final theorem.

## Evidence convention

Each row below has an individual successful compiler entry and a match of its current recursive local source closure to the manifest. The complete final run also has no source drift. Logs supply the printed axiom reports. The audit script does not itself compile Lean; the actual compiler manifests are the primary evidence. External compiler and precompiled dependency hashes are recorded in the manifests. The certificate package additionally binds included source files and compiled `.olean` proof artifacts by SHA-256.

All module names below have prefix `Classicism.Results.Research.`. The transitive local Classicism dependencies, including Boolean-valued soundness and the object-language C proof infrastructure, are included in the package and compiler manifests.

| Checked module | Compiler manifest | Compiler log |
| --- | --- | --- |
| `MaxAtomicityCanonicalCompletion` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T054110843342Z-8be037f2/Classicism_Results_Research_MaxAtomicityCanonicalCompletion.log) |
| `MaxAtomicityCodedFunctions` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T053534142668Z-b0a0c6da/Classicism_Results_Research_MaxAtomicityCodedFunctions.log) |
| `MaxAtomicityConcreteModel` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T050626811631Z-7bdcce28/Classicism_Results_Research_MaxAtomicityConcreteModel.log) |
| `MaxAtomicityCountableGenerator` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044931008757Z-62784d6f/Classicism_Results_Research_MaxAtomicityCountableGenerator.log) |
| `MaxAtomicityEvalTools` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044202659356Z-94ef85a2/Classicism_Results_Research_MaxAtomicityEvalTools.log) |
| `MaxAtomicityHCodeCharacterization` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T045523774389Z-b6960aa2/Classicism_Results_Research_MaxAtomicityHCodeCharacterization.log) |
| `MaxAtomicityHCodeExistence` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T045523774389Z-b6960aa2/Classicism_Results_Research_MaxAtomicityHCodeExistence.log) |
| `MaxAtomicityHCodeSemantics` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044931008757Z-62784d6f/Classicism_Results_Research_MaxAtomicityHCodeSemantics.log) |
| `MaxAtomicityHCodeSyntax` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T042947565669Z-a7427a13/Classicism_Results_Research_MaxAtomicityHCodeSyntax.log) |
| `MaxAtomicityHereditaryCover` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044202659356Z-94ef85a2/Classicism_Results_Research_MaxAtomicityHereditaryCover.log) |
| `MaxAtomicityHereditaryGraphs` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T052556133859Z-c359be20/Classicism_Results_Research_MaxAtomicityHereditaryGraphs.log) |
| `MaxAtomicityHereditaryUniverse` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044202659356Z-94ef85a2/Classicism_Results_Research_MaxAtomicityHereditaryUniverse.log) |
| `MaxAtomicityInconsistency` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T054730505817Z-9a834f08/Classicism_Results_Research_MaxAtomicityInconsistency.log) |
| `MaxAtomicityJechShelahAmalgamation` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051417824651Z-594808da/Classicism_Results_Research_MaxAtomicityJechShelahAmalgamation.log) |
| `MaxAtomicityJechShelahArithmeticExistence` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T054627454428Z-7a9dd757/Classicism_Results_Research_MaxAtomicityJechShelahArithmeticExistence.log) |
| `MaxAtomicityJechShelahArithmeticSemantics` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T054333343375Z-85343c9c/Classicism_Results_Research_MaxAtomicityJechShelahArithmeticSemantics.log) |
| `MaxAtomicityJechShelahBranch` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051652660156Z-72daa52e/Classicism_Results_Research_MaxAtomicityJechShelahBranch.log) |
| `MaxAtomicityJechShelahConditionSemantics` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T054627454428Z-7a9dd757/Classicism_Results_Research_MaxAtomicityJechShelahConditionSemantics.log) |
| `MaxAtomicityJechShelahCylinders` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T050626811631Z-7bdcce28/Classicism_Results_Research_MaxAtomicityJechShelahCylinders.log) |
| `MaxAtomicityJechShelahEnumeration` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T045523774389Z-b6960aa2/Classicism_Results_Research_MaxAtomicityJechShelahEnumeration.log) |
| `MaxAtomicityJechShelahFiniteRefinement` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051652660156Z-72daa52e/Classicism_Results_Research_MaxAtomicityJechShelahFiniteRefinement.log) |
| `MaxAtomicityJechShelahFusion` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T050528283445Z-e13f0a58/Classicism_Results_Research_MaxAtomicityJechShelahFusion.log) |
| `MaxAtomicityJechShelahIndexCoding` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051652660156Z-72daa52e/Classicism_Results_Research_MaxAtomicityJechShelahIndexCoding.log) |
| `MaxAtomicityJechShelahIndexedGenerators` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051417824651Z-594808da/Classicism_Results_Research_MaxAtomicityJechShelahIndexedGenerators.log) |
| `MaxAtomicityJechShelahLocalFusion` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T053534142668Z-b0a0c6da/Classicism_Results_Research_MaxAtomicityJechShelahLocalFusion.log) |
| `MaxAtomicityJechShelahLocalStage` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T053534142668Z-b0a0c6da/Classicism_Results_Research_MaxAtomicityJechShelahLocalStage.log) |
| `MaxAtomicityJechShelahRigidityCriterion` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051417824651Z-594808da/Classicism_Results_Research_MaxAtomicityJechShelahRigidityCriterion.log) |
| `MaxAtomicityJechShelahSetCodes` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051652660156Z-72daa52e/Classicism_Results_Research_MaxAtomicityJechShelahSetCodes.log) |
| `MaxAtomicityJechShelahSyntax` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051417824651Z-594808da/Classicism_Results_Research_MaxAtomicityJechShelahSyntax.log) |
| `MaxAtomicityJechShelahTrees` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T045523774389Z-b6960aa2/Classicism_Results_Research_MaxAtomicityJechShelahTrees.log) |
| `MaxAtomicityMostowski` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044202659356Z-94ef85a2/Classicism_Results_Research_MaxAtomicityMostowski.log) |
| `MaxAtomicityPureSelector` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051417824651Z-594808da/Classicism_Results_Research_MaxAtomicityPureSelector.log) |
| `MaxAtomicityReduction` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T043512624964Z-73db32d1/Classicism_Results_Research_MaxAtomicityReduction.log) |
| `MaxAtomicityRegularCompletion` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044202659356Z-94ef85a2/Classicism_Results_Research_MaxAtomicityRegularCompletion.log) |
| `MaxAtomicityRegularOpenCode` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T050111756968Z-5163557c/Classicism_Results_Research_MaxAtomicityRegularOpenCode.log) |
| `MaxAtomicityRigidTransport` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044931008757Z-62784d6f/Classicism_Results_Research_MaxAtomicityRigidTransport.log) |
| `MaxAtomicitySelectorTransport` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T054110843342Z-8be037f2/Classicism_Results_Research_MaxAtomicitySelectorTransport.log) |
| `MaxAtomicitySetCodeAbsoluteness` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T053534142668Z-b0a0c6da/Classicism_Results_Research_MaxAtomicitySetCodeAbsoluteness.log) |
| `MaxAtomicitySetFormulaTools` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T045523774389Z-b6960aa2/Classicism_Results_Research_MaxAtomicitySetFormulaTools.log) |
| `MaxAtomicitySetSemantics` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044202659356Z-94ef85a2/Classicism_Results_Research_MaxAtomicitySetSemantics.log) |
| `MaxAtomicitySetSyntax` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T042947565669Z-a7427a13/Classicism_Results_Research_MaxAtomicitySetSyntax.log) |
| `MaxAtomicitySlalomInvariance` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044931008757Z-62784d6f/Classicism_Results_Research_MaxAtomicitySlalomInvariance.log) |
| `MaxAtomicitySlalomLimit` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T051652660156Z-72daa52e/Classicism_Results_Research_MaxAtomicitySlalomLimit.log) |
| `MaxAtomicitySlalomThinning` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T045523774389Z-b6960aa2/Classicism_Results_Research_MaxAtomicitySlalomThinning.log) |
| `MaxAtomicitySplitCertificate` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T043512624964Z-73db32d1/Classicism_Results_Research_MaxAtomicitySplitCertificate.log) |
| `MaxAtomicitySplitSemantics` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T050111756968Z-5163557c/Classicism_Results_Research_MaxAtomicitySplitSemantics.log) |
| `MaxAtomicitySyntax` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T042947565669Z-a7427a13/Classicism_Results_Research_MaxAtomicitySyntax.log) |
| `MaxAtomicityWellOrder` | [20261023T054730505817Z-9a834f08](checks/20261023T054730505817Z-9a834f08.json) | [log](logs/runs/20261023T044202659356Z-94ef85a2/Classicism_Results_Research_MaxAtomicityWellOrder.log) |

## Reproduction with the existing installation

Run from the bundle root under the authorized serial compiler owner. The existing installation suffices; no download was needed. The five explicit Mathlib targets compensate for the shared import parser omitting `public meta import`.

```sh
/tmp/classicism-followup-venv/bin/python3 \
  research/2026-10-22/lean-formalization/check_with_mathlib.py \
  Mathlib.Lean.Expr.Rat \
  Mathlib.Algebra.Order.Ring.Unbundled.Rat \
  Mathlib.Tactic.Ring.Basic \
  Mathlib.Data.PNat.Basic \
  Mathlib.Util.AtomM.Recurse \
  Classicism.Results.Research.MaxAtomicityInconsistency \
  --cache /tmp/classicism-max-integrated-cache \
  --source-root /tmp/classicism-max-missing-sources \
  --timeout 120 --lock-wait 300 --keep-going
```

The wrapper reads [mathlib-dependencies.json](mathlib-dependencies.json): Lean 4.33.1 at `/tmp/classicism-lean-toolchain/lean-4.33.1-darwin_aarch64/bin/lean`, Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, and installed binary roots under `/tmp/classicism-mathlib/.lake/`. The package contains the checked local proof objects and sources; it does not bundle the external Lean/Mathlib installation. Inspect the immutable run manifest rather than `last-check.json`, which can belong to another task.

No YAML verdict, generated statement, or `lean: verified` registry field was changed manually. The successful compiler evidence above is the verification claim. The older `max-atomicity-checked-background-certificates.zip` is a retained partial checkpoint; use the complete package linked above.

Work is complete and stops before the user’s 2026-10-23 05:57 UTC cutoff. No goal, automation, or autonomous follow-up was created.
