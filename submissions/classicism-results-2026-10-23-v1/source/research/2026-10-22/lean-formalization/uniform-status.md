# Uniform comprehension and evaluator integration

Compiler: Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
The serial `check_module.py` driver uses `/tmp/classicism-lean-cert-cache`, never
downloads or runs Lake, and records source/dependency fingerprints in `checks/`.

## Checked certificates

`Classicism.Results.Research.UniformHalfComprehensionCertificates` exits 0.
Both source modules pass the closed-argument gate and relational-type audit.
The positive-evaluator/Actuality equivalence, actual-world uniqueness and local
Barcan lemma translate into C derivations. All four uniform converse rules and
the three forward rules have genuine C certificates. The unary converse rules
explicitly assume Existence of the argument type; their generated list rules
explicitly assume tuple existence. Nullary converses have no such premise.

`UniformHalfComprehensionClosed` also exits 0: it discharges tuple existence in C
at every finite list of closed types, including the empty list. Thus the three
exact equivalences are certified at every fixed admitted relational type, with
no optional premise. Full uniform Inextensible Comprehension is certified only
in the direction to Actuality. The wrapper's axiom report contains only
`propext` and `Quot.sound`, used in metatheory of the object-language derivations.

Sources: `../notes/uniform-half-comprehension-definitions.md` and
`../proof-refinements/canonical-actual-evaluator.md`, §§1–2. The normalized
canonical evaluator and quantifier identities are not yet claimed certified.
No YAML, generated Statements, or source proof was modified.

## Integration of handed-off modules

`Classicism.Results.Research.AtomCoordinates` and `BoundedSplitter` both exit 0
with gate/type checks and requested derivations. The atom module additionally
produces three rules and their list forms. Repairs replaced same-module audits
(the auditor only sees imported modules) by explicit theorem checks, and declared
the three schemas before requesting their list forms. Mathematical statements
and proofs were retained. Locate durable evidence in `checks/` by the manifest's
`modules` field; timestamps there are machine UTC, not user-facing research dates.
