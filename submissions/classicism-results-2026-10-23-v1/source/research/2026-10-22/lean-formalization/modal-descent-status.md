# Rigidity closure and descent handoff

**READY FOR INTEGRATION.** These five new files are frozen and ownership
passes to sole compiler/integrator `01a1664d-7c13-7701-b52c-2070ee16eb06`.
No Lean/Lake execution, dependency installation, new agent, or parallel
build was performed by this author. All formal checks remain pending.

| Module suffix | Source SHA-256 |
| --- | --- |
| `ModalRigidityDescent` | `54b20884593184d4b405c273c766a5f967410974242e784ad5ad580181d8e820` |
| `ModalRigidityDescentCertificates.IndexedUnion` | `593bf7ac50e9b4a4b313bb23c2e4a1d6b348d5e83cecb89e77c85cb1f9dc543a` |
| `ModalRigidityDescentCertificates.DirectImage` | `e8811cfd4de4dd0a2ce8dc3409352359416ee5bdbf41775e544443d52c91a496` |
| `ModalRigidityDescentCertificates.InverseImage` | `d34df8e2bb41e5280218c7858e17a6a477cd8112f21dcfd5378bea5774b3613a` |
| `ModalRigidityDescentCertificates.Comprehension` | `6ce9cb95d106ceaa6f0f90a1fecfe81f8e11d7187f327efefa484f073140e1c3` |

The referee-level argument is in `modal-rigidity-descent.md`. The main new
results are rigid indexed unions from a rigid index set and current rigid
fibers, direct-image closure, inverse-image closure under necessarily
injective maps and a sealable image restriction, and comprehension descent
along such maps. The indexed-union theorem admits individual argument
and output positions through a relational family. The operation-based
image/descent results have relational output types, as required by C.
They assume no BF, choice or ND. The comprehension-descent theorem has its
explicit RC premise; no new axiom or unproved model is used.

The shallow source contains gate/type audit directives. Each of the four
certificate modules translates one substantive target, in a dependency
chain sharing generated declarations. Their `.derivable` statements are
object-language C proofs of the displayed typed formulas, conditional only
on their explicit hypotheses. They are not extra database schema records.
No tuple or all-schema theorem is inferred from an ordinary compilation.

After the core owner finishes dependency setup, the exact shallow command is:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ModalRigidityDescent --timeout 180
```

The serial terminal target for the certificate chain is:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.ModalRigidityDescentCertificates.Comprehension --timeout 180
```

Its first certificate imports `ModalPropagationSchemas` to continue the
shared translation environment without duplicate generated declarations.
The shallow proof module itself is independent of the propagation drafts,
so it can be checked while that heavier certificate chain is pending. If
necessary, the integration owner may move certification to its existing
shared environment rather than waiting on an unrelated compilation issue;
that does not change the source theorem or its scope.

Preserve per-check logs and verify each `.derivable` type and axiom report.
Repository validation passed after this batch (132 principles, 447 results,
162 models); this is not evidence of Lean elaboration or C certification.
No original research, generated statement, source proof or YAML flag was
changed. The remaining proposed forcing/symmetric countermodels retain the
specific construction and satisfaction obligations in `modal-status.md`.
