# Full modal-schema continuation

**READY FOR INTEGRATION.** These six fresh modules are frozen and handed to
sole compiler/integrator `01a1664d-7c13-7701-b52c-2070ee16eb06`. The earlier two
modules and fourteen standalone checks remain frozen. No Lean/Lake process
has been run by this author. All compile, gate, type, derivation and schema
checks for this continuation remain pending.

This supersedes only the unfinished-composition section of `modal-status.md`:
the full finite implications and all-schema compositions are now supplied as
source drafts. It does not upgrade the verification status of any theorem.

| Module suffix | Source SHA-256 |
| --- | --- |
| `ModalPropagationConsequences` | `89a6f5fb52537293f8f4926589667f2b76526e0588ab1a2145f1a76c821386d7` |
| `ModalPropagationCertificates.StableLeibniz` | `60aec6cd239e3efff16855d3b5ba0df5c7370db67382f9fd24e1bce044859ea6` |
| `ModalPropagationCertificates.BoxedBarcan` | `ff8e59ac55f944dc1f04254faaed525e852797451a7c0875372116373d8eb19f` |
| `ModalPropagationCertificates.BoxedComprehension` | `bf6fc220f81ce0d71f3831b09d92060e59e5127668bfa43111e70e857773ce0b` |
| `ModalPropagationCertificates.BoxedCompleteness` | `b42c2e63870a7b3d4acdea43a666656bf12c899324d44f4b4a2369114893d3a1` |
| `ModalPropagationSchemas` | `c2cc7407d22df74d9e9ee95f9be397f890b0ee1ed2c65625f390ea764fe6022c` |

The new `ModalPropagationConsequences.lean` removes the explicit RP premise
using the recorded `atom_rc_rigid_power` and SL implying Atomicity. It supplies
three substantive typed conclusions: boxed relational BF from four local
instances, and boxed RC and BC from nine local instances. All nine premises
are instances of Strong Leibniz or Rigid Comprehension. BF_e is absent.

The four `ModalPropagationCertificates` modules form a dependency chain,
with one new certificate target per compilation process. Each requests both
`#classicism_certify` and `#classicism_entails`. Importing the existing Arity
layer before new translation, and then importing the preceding certificate,
gives generated dependencies a shared home rather than independently
redeclaring them. Do not import the earlier standalone diagnostic drivers
together into this chain.

`ModalPropagationSchemas.lean` assembles the generated list entailments with
`schema_subset_args`. Its intended final theorem is

```
StrongLeibniz.schema ∪ RigidComprehension.schema
  entails NecStrongLeibniz.schema ∪ NecBarcanRelational.schema
          ∪ NecRigidComprehension.schema ∪ NecBooleanCompleteness.schema.
```

Parentheses in the actual declaration specify left-associated union. These
are metalogical entailments of C certificates; there is no quantifier over
types in an object-language formula. The finite-tuple and empty-tuple claims
rely on actual list certificates being produced. A missing generated
`.listEntails`, failed vectorization, or type mismatch blocks the final
module and must be repaired or recorded, not bypassed with an axiom.

## Exact serial check command

After setting up the dependency-aware certification runtime, the sole owner
can use the existing runner in the order recorded in
`modal-continuation-manifest.json`. The terminal target includes that order
through imports:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ModalPropagationSchemas --timeout 180
```

Run only one such process. The original runner currently rejects missing
Mathlib imports, so dependency setup remains the core owner's responsibility.
Preserve each check's fingerprint/log and inspect the actual `.rule`,
`.listRule`, `.listEntails` and final entailment types before marking complete.
After repairs, run the normal repository validator.

## Earlier diagnostic-driver correction for the integration owner

`modal-checks/ModalRigidUniverse.lean` currently asks `#classicism_certify` for
an Iff-shaped theorem, `universe_rigid_iff_necessary_barcan`. Inspection of
`Tools/Schema.lean` shows that the certification command expects a principle
implication shape. The intended correction is to use `#classicism_derive`
for that exact theorem, or first introduce a named closed law and certify its
proof. This author did not edit the frozen driver after noticing this.
The four new certificate targets already have the required principle shape.

Repository validation passed after the new module batch. No record YAML,
source proof, generated statement, toolchain or shared engine was edited.
