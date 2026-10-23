# ND + Inextensible Comprehension: certified

The complete local theorem has passed shallow compilation, the Classicism
closed-argument gate, the relational-type audit, and translation to a genuine
object-language C derivation and schema rule:

    ND_t + IC_(tau -> t) -> WeaklyRigidPower_tau.

Both optional premises are current, unboxed. The generated `.listRule` has type
indices `tau = sigma_s ⇒* t` for **every finite argument list**, including the
empty list. No extra existence, BF, BC, RC, or globally boxed ND premise remains.

Main source module:
`topics/classicism/lean/Classicism/Results/Research/InextensibleWeakPower.lean`.
Main driver: `InextensibleWeakPowerCertificates.lean`, same directory.
Main declaration:
`Classicism.Research.InextensiblePower.nd_ic_weaklyRigidPower.rule` and `.listRule`.
The kernel axiom report for the C derivation is `[propext, Quot.sound]`, in the
metatheory; the shallow gate enforces C's restriction on those principles.

Reusable checked intermediate modules provide:

- persistent falsity under current ND_t;
- persistent necessarily separated relations equal their IC coextensions;
- weak-rigidity squares and necessary internal separation;
- exact local `ND_t + IC_tau -> TameRigidity_tau`;
- `IC_(tau t) -> IC_tau` and the corresponding weak-IC descent;
- `ND_t + IC_(tau t) -> RigidPower_tau`;
- bounded weak rigidity becoming rigidity under internal separation.

The descent proof is a new haecceity-pullback presentation, reusing the checked
ModalPropagation pullback lemma. It replaces neither the original union argument
nor the frozen source note. Mathematical source: the original unpaginated
`../notes/nd-inextensible-comprehension-implies-weak-power.md`, §§1–6 (`misc`).

Reproduce serially from the bundle root:

```sh
/tmp/classicism-followup-venv/bin/python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.InextensibleWeakPowerCertificates
```

The successful run and source/dependency fingerprints are in `checks/`; full
output is in `logs/Classicism_Results_Research_InextensibleWeakPowerCertificates.log`.
No database record was created, and no `lean: verified` status was set manually.
