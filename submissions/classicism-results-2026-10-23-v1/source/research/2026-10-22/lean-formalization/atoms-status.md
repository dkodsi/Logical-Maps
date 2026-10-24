# Atom-coordinate and splitter formalization

**READY FOR INTEGRATION.** Source ownership transferred to the existing Lean task;
this drafting agent has frozen both modules. The integration owner may repair and
compile them serially. Compilation and Classicism certificate checks remain pending.

SHA-256 at handoff:

| Module | SHA-256 |
| --- | --- |
| `AtomCoordinates.lean` | `189ec93a43f5260b14c0db09a39fb73cf64ce73a41425a305f931b7fba25aa3d` |
| `BoundedSplitter.lean` | `f5715202a3b525599f4db126992acdd9b88f19ee11bd734da03bbf8d75862aed` |

Repository validation passed: 132 principles, 447 results, 162 models.

Drafted 22 October 2026. Direct source: the companion research notes, not a published
attribution. No independent or formal verification claim until the serial compiler
owner executes the commands at the foot of each new module.

Modules:

- `topics/classicism/lean/Classicism/Results/Research/AtomCoordinates.lean`:
  unary projection, pinning, exact current-witness criterion, local/full BF
  classification, collision, ND/injectivity, the projection adjunction, and
  Atomicity transfer in both directions under unary BF.
- `topics/classicism/lean/Classicism/Results/Research/BoundedSplitter.lean`:
  the bare-C guarded splitting lemma and unboxed Atomicity obstruction.

The collision theorem is stronger than the source atom-only statement: it holds
for arbitrary proposition scalars. The ND injectivity direction only needs a
nonzero scalar. The reverse direction retains Atomicity_t.

Scope is explicit: the atom module targets the unary core, with three closed
schema wrappers asking the standard pipeline for finite-tuple versions of
projection, pinning, and collision. A tuple claim requires a produced `.listRule`;
no all-tuples result is inferred merely from unary BF. The splitter module does not prove the rigid
Boolean model/coding construction, and does not claim Max + Atomicity inconsistent.
No source records, generated statements, or existing proof modules were edited.

Each module has the Classicism gate/type audits followed by object-language
derivation commands. These commands still need execution. No new axioms, `sorry`,
unrestricted Choice, or hypothesis-dependent extensionality were introduced.
