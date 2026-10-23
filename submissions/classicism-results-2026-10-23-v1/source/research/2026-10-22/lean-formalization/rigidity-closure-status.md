# Rigidity and Boolean closure formalization handoff

Status: **READY FOR INTEGRATION — source files frozen**. This author has not run
Lean, Lake, the serial check runner, a package download, or a graphical display.
The sole compiler/integrator owns repairs and certification after this handoff.
These are complete proof bodies without proof holes, rather than statement-only
stubs or theorems assuming their decisive mathematical steps. No successful Lean
check is claimed here.

## Mathematical content implemented

1. **Generation and joins.** Weak rigidity is exactly being the represented join
   of the current singleton family; full rigidity is the necessity of that
   reconstruction. Existing represented joins preserve persistence, weak
   inextensibility, and weak rigidity. The indexing family itself need not be
   rigid, and completeness is not assumed. Tame Rigidity is exactly closure of
   rigid relations under existing represented joins.
2. **Exact finite Boolean closure.** At an argument type σ, local ND_σ is
   equivalent to intersection, relative-difference, and symmetric-difference
   closure, separately for weakly rigid and rigid properties of σ-objects. It is
   also equivalent to all their current instance values being top or bottom.
   Finite union closure requires no optional premises. The decisive cut lemma
   seals membership decisions inside the rigid bound rather than applying
   current ND to arbitrary future objects.
3. **Exact complement costs.** Weak complement closure at σt is equivalent to
   ND_σ + BF_σ; rigid complement closure is equivalent to ND_σ + □BF_σ.
   Either complement closure at tt alone is equivalent to □ND_t (C5), and C5
   supplies both complement closures at every argument type.
4. **Comprehension classification.** A direct singleton-join argument proves
   local ND_σ + BC_(σt) implies Weak Rigid Comprehension_(σt). Combining this
   with the independently implemented ND + IC machinery gives full-schema
   IC ⇔ RC ⇔ TR ⇔ WRP over the unboxed base ND + BC. The higher-type RC premise
   needed for WRP is displayed explicitly in the finite-instance arrow; the
   final equivalence is assembled as metalogical entailment between schemas.

The certificate drivers request the C gate, relational type audit, actual
translated C derivations, and finite-tuple/list rules. Missing list rules are
explicit failures. Thus the nullary t case is not silently inferred from an
inhabited external unit sort. The final schema assembly identifies every
relational type with its argument list ending in t. No schema quantifies over
object-language types.

## Stage 1 tracked inventory mapping (historical; see Stage 2 below)

These are source-implementation statuses, not successful Lean checks.

| Tracked key | Coverage in this frozen batch |
| --- | --- |
| `rigidity.01` nullary rigidity | Not implemented here; remains an explicit queue item. |
| `rigidity.02` Atomicity + RC ⇒ WRP | Not implemented here; remains an explicit queue item. |
| `rigidity.04` singleton reconstruction | Full proof bodies in `RigidityClosureResearchJoins`; unary necessary version and requested tuple certificates for reconstruction. |
| `rigidity.05` existing joins and TR | Full proof bodies in `RigidityClosureResearchJoins`; requested tuple certificates for join closure and the exact TR characterization. |
| `rigidity.06` ND equivalence package | Intersection, difference, symmetric difference and pointwise bivalence implemented in `RigidityClosureResearchFinite`. Section closure is not implemented in this batch and is assigned to the separate sections/retractions owner. Thus this aggregate key is only partially covered here. |
| `rigidity.07` complement closure | Full exact local/boxed BF characterizations and low-type C5 equivalences in `RigidityClosureResearchFinite`; all-type C5 consequences in Classification. |
| `rigidity.08` bounded propagation gap | Not newly implemented here. Existing `InextensibleWeakPower.bounded_tame` is reused only for the previously implemented WRP theorem; the exact TR+RP+H decomposition is still a separate coverage item. |
| `rigidity.10` ND+BC classification | Full finite-instance arrows plus full-schema IC/RC/TR/WRP mutual entailments in Classification and Schemas. |
| `rigidity.11` uniform rigidification | Not implemented here; preserve as an explicit item for the sections/retractions/comprehension owner. |
| `rigidity.12` Boolean interval and complete retraction | Only join/finite-closure prerequisites supplied here. The representation maps, uniform normalizer, and complete-retraction theorem remain with the sections/retractions owner. This aggregate key is not complete. |

## Sources and scope

Direct sources (original research, unpaginated, source category `misc`):

- `research/2026-10-22/notes/rigidity-by-joins-and-boolean-closure.md`, §§1–2.
- `research/2026-10-22/notes/rigid-boolean-closure.md`, §§1–4,6–7 (the membership
  bivalence part of §7; section closure is assigned elsewhere).
- `research/2026-10-22/notes/nd-inextensible-comprehension-implies-weak-power.md`,
  §7, “Exact classification over ND + BC”.

Definitions were checked against the topic background and ND, BC, IC, RC, TR,
WRP and BF principle records. Existing universe/Barcan and singleton lemmas are
reused. The new proofs do not add mathematical axioms, BF_e, Choice, full
extensionality, e-valued operations, or a language extension. No source note,
model record, generated Statements.lean or YAML verdict was changed.

This lane does **not** implement the old/new countermodel to ND + BC ⇒ RC;
that separate semantic construction has another owner. It also does not claim
RP equivalent to these principles, nor TR+RP⇒WRP.

## Serial check targets

Run from the bundle root, by the sole compiler owner, in this order:

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RigidityClosureResearchFiniteCertificates
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RigidityClosureResearchJoinsCertificates
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RigidityClosureResearchClassificationCertificates
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RigidityClosureResearchSchemas
```

The final target imports the preceding certificate chain, so a single run of
that target is also sufficient. If the sizeable certificate driver times out,
its individual commands may be split into sequential drivers without relaxing
any audit or requested list certificate.

## Author checks

Repository validation passed after each edit batch: **132 principles, 447
results, 162 models — OK**. See `rigidity-closure-validation.log`. A static
noncompiler scan found balanced delimiters and no `sorry`, `admit`, or `axiom`
declarations. Those checks do not establish elaboration or C certification.
No mathematical gap was left as a premise in these source proofs. Potential
remaining work is elaboration, translation and schema-generator integration;
only the compiler can establish their success.

## Frozen source SHA-256

All paths below are under `topics/classicism/lean/Classicism/Results/Research/`.

- `RigidityClosureResearchClassification.lean`: `668fe461733ce9bc64e063c5e5551fde1a6671c3c1167f7ce2282cbbb1b19625`
- `RigidityClosureResearchClassificationCertificates.lean`: `8adb65aa75552cedb7dab845881e01ac68652b241293a002bc7ad61aa97075a7`
- `RigidityClosureResearchFinite.lean`: `d7fa4156fa27377a3e43bf8f37587550c29b6f5b19dc10ddda59faf3aa91f236`
- `RigidityClosureResearchFiniteCertificates.lean`: `8ed19adb372d5286ad311abad15c76f048a1e3563ce2e7bcea2912b8adde592a`
- `RigidityClosureResearchJoins.lean`: `e76ebcc0b34a0d2d9f1854e2cd05526628345010bd25d3337bd0d041faad066c`
- `RigidityClosureResearchJoinsCertificates.lean`: `36a9f94701246f11ae71c9aa7ee286686c26649493947fb9b18a37a3d70dc6c1`
- `RigidityClosureResearchSchemas.lean`: `65aafd12759579186d8fa5fbb481970486fc6c7c4d9ba8aac0000f0d4b50f6f7`


## Stage 2: all remaining assigned families implemented — READY FOR INTEGRATION

**All twenty files are now frozen for the sole compiler/integrator.** Stage 1
files are unchanged. This continuation adds thirteen sources/drivers. All
claims below are source implementation claims; none has been compiler checked
by this author. The complete dependency chain is intended to fail if a gate,
type, C derivation, finite-tuple certificate, or schema entailment is missing.

### Current key-by-key mapping

| Tracked key | Current source coverage |
| --- | --- |
| `rigidity.01` | `Nullary`: WeakRigid(p) iff p is top/bottom iff Rigid(p); C proofs of nullary TR, RP, WRP, Rigid Rigidity, Weakly Rigid Weak Rigidity, RC and WeakRC, with the indicated necessary versions. This key concerns nullary rigidity; no internally finite power theorem is inferred. |
| `rigidity.02` | `AtomicPower`: full atom-pullback proof of Atomicity_(τt) + RC_τ ⇒ WRP_τ, plus the correctly boxed counterpart. No ND, BF or higher RC hypothesis is used. The all-schema consequence is in `ContinuationSchemas`. |
| `rigidity.04` | `Joins` plus `TupleLaws`: singleton reconstruction and its necessary counterpart, with explicit finite-tuple certificate requests for both. |
| `rigidity.05` | `Joins`: existing represented joins preserve weak rigidity; TR iff rigid-join closure. |
| `rigidity.06` | `Finite`: intersection/difference/symmetric-difference/bivalence characterizations at weak and rigid levels. **Section closure remains assigned to the other sections/retractions owner**, so this aggregate key is not wholly completed by this lane. |
| `rigidity.07` | `Finite`, `Classification`, `TupleLaws`: exact weak BF versus rigid boxed-BF complement characterizations, low-type C5 equivalence, and all-type C5 consequences. |
| `rigidity.08` | `Bounded`: WRP ⇒ bounded future tameness; TR + RP + bounded future tameness ⇒ WRP; argument-type ND supplies the bounded condition. `ContinuationSchemas` proves the exact all-schema decomposition. The WRP⇒RP direction explicitly uses the higher WRP instance; no unsupported fixed-type implication is claimed. |
| `rigidity.10` | `Classification`, `Schemas`: exact ND+BC classification IC ⇔ RC ⇔ TR ⇔ WRP, with the higher-type route made explicit. |
| `rigidity.11` | `Uniform`, `ContinuationSchemas`: uniform weak/rigid comprehension iff the ND strengthening of the corresponding full comprehension schema. Direct actual-evaluator⇒ND proof; single unary uniform instances imply ND/Actuality with explicit current Existence, while full-schema equivalence uses its nullary instance and requires no extra axiom. |
| `rigidity.12` | `Retractions`: explicit map Y↦c(w)∧Y, support/order reflection/injectivity/surjectivity onto [0,c(w)], admitted fragment completeness and units, inverse normalizer identities, finite Boolean laws, complete represented-join preservation, exact empty-relation kernel/interval, and ambient relative-complement closure under ND. The main theorem packages derive actual-world existence and ambient completeness from the displayed higher comprehension instances. |

The `.12` representation is expressed by the actual C formulas for an order
isomorphism and admitted completeness, rather than an external Lean
`BooleanAlgebra` class substituted for the original intensional domains.
Normalizers operate on admitted relation types only. Their equations are local
universal statements; only each fixed-argument identity can be necessitated.
The fragment unit is not identified with the ambient top relation.

### Stage 2 mathematical dependencies and remaining obligations

The nullary and atom-pullback proofs follow `notes/maximalism-modal.md`, §§15–16.
The bounded-propagation decomposition follows §§18–19, preserving its full-schema
scope. Uniform rigidification follows §22; the complete interval/retraction
proofs follow `notes/rigidity-by-joins-and-boolean-closure.md`, §§4–6 and
`notes/maximalism-modal.md`, §23. All are original research (`misc`), unpaginated.
Existing compiled-source candidates for singleton rigidity, WI bounded tameness,
actual-world localization, and evaluation of represented joins are reused with
their precise assumptions.

No proof body assumes its decisive mathematical step. No mathematical gap was
left unresolved in this lane's stated coverage. Remaining execution work is
Lean elaboration, C gate/type translation, the requested tuple certificates,
and schema assembly. Source-level static review cannot certify those steps.
The old/new countermodel and `.06` section closure remain with their assigned
owners. None of these files certifies the old/new countermodel by implication.

### Exact single serial command

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.RigidityClosureResearchContinuationSchemas
```

That target checks both stages. For staged serial runs, the driver import order
(after the Stage 1 `RigidityClosureResearchSchemas` target) is:

1. `Classicism.Results.Research.RigidityClosureResearchTupleLawsCertificates`
2. `Classicism.Results.Research.RigidityClosureResearchNullaryCertificates`
3. `Classicism.Results.Research.RigidityClosureResearchBoundedCertificates`
4. `Classicism.Results.Research.RigidityClosureResearchAtomicPowerCertificates`
5. `Classicism.Results.Research.RigidityClosureResearchUniformCertificates`
6. `Classicism.Results.Research.RigidityClosureResearchRetractionsCertificates`
7. `Classicism.Results.Research.RigidityClosureResearchContinuationSchemas`

Each imports the preceding driver, so successful checks can be cached. A large
driver may be split into sequential single-target drivers by the integrator;
no check should be dropped. The author ran no compiler or package installer.
Repository validation passed after every batch and final status edit. Static
no-proof-hole and balanced-delimiter checks passed for all twenty files.

### Stage 2 frozen SHA-256

- `RigidityClosureResearchAtomicPower.lean`: `dbd4503280674c4407e3b848e269de23fa79589187caa23d2eb78665f59b4112`
- `RigidityClosureResearchAtomicPowerCertificates.lean`: `b8f8aa4045d5dd104b4fcb7de23a7619c2e59a627290b76d2ab6162b5c05491c`
- `RigidityClosureResearchBounded.lean`: `65a1109a5213f8456937a2c344d98e2e94074c0c1ffaff6a02b14b9f1349b628`
- `RigidityClosureResearchBoundedCertificates.lean`: `c6ab51e9f6feed79a9615ec9557b496713fc1a91df92029a63cc68c77960e644`
- `RigidityClosureResearchContinuationSchemas.lean`: `8797ae790b2015ed511d1b695641b2eb983648b632722c9c43cf19bf65351896`
- `RigidityClosureResearchNullary.lean`: `8a03deb010dce7238ef0f5c5d20dd14a16f6ba5ae97cb7e409b13375ce7c5f1f`
- `RigidityClosureResearchNullaryCertificates.lean`: `d69ae7225edf4402ed3c59a53fc395bbabe8ad92d35b77d78a22c273e07e843f`
- `RigidityClosureResearchRetractions.lean`: `a316e5405520c1f97791c0dc1bc917fab5b98fc36083a4ed04824c255f385416`
- `RigidityClosureResearchRetractionsCertificates.lean`: `26a2c693945a4117483e595ebc9b66b276ca89a7e9c4a208238f836eb7ecdd87`
- `RigidityClosureResearchTupleLaws.lean`: `3a5a3aff5db6e339088e76cf71138774d568aa397a9cf0b887d11497eeb67597`
- `RigidityClosureResearchTupleLawsCertificates.lean`: `61aeef1fbef668db056c51d7a1c28c715a63be3dd2ec4e222c72c9d9400e722e`
- `RigidityClosureResearchUniform.lean`: `45edb0d226292e20cc7c23b8b00a5638f4276a9271821bba0eca91269bc411d8`
- `RigidityClosureResearchUniformCertificates.lean`: `fbb691fb9ac91cc5c54c36fa887e86c17dd915351950d10e65884fab6861030b`
