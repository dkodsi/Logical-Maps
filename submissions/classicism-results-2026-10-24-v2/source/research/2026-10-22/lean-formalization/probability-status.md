# Probability formalization status

**READY FOR INTEGRATION. All 15 modules listed below are frozen for the sole serial integrator.** The probability author has run no Lean/Lake commands, downloads or parallel builds. The integrator may repair these files; handoff hashes remain immutable.

## Verified so far

The first five algebra modules passed ordinary Lean checking in [the serial manifest](checks/20261023T022700791873Z.json). This establishes conditional external algebra only. The [axiom report](logs/Classicism_Results_Research_AtomicProbabilityAlgebraChecks.log) shows axiom-free envelope totality, additivity, residuals and saturation comparison; enumeration-based averages and finite-fibre proofs currently report **Classical.choice** (plus propext/Quot.sound). Do not call those Lean proofs choice-free. A constructor-based replacement module is ready for checking below.

The remaining files have author drafts and requested checks; no success, gate/type pass or object-language certificate is claimed here for them. Repository validation passed after every edit batch: **132 principles, 447 results, 162 models**.

## Coverage and precise gaps

- **External conditional algebra:** canonical supremum graph, finite additivity, atom values, positivity and residual; finite-class average graph/mass preservation/idempotence; finite-fibre finite-budget estimate; complete additivity from explicit finite-cover/subjoin resources; normalization by a supplied positive additive order isomorphism. Internal instances are not supplied.
- **Fixed C-language cut infrastructure:** bounded cut-union LUBs; conditional literal code uniqueness; graph addition, cut order/additive closure and principal embedding; rounded complement reflection and involution. Current premises only. Certificates are requested in separate modules. No external Nat/List or forbidden individual-valued operation occurs in this family.
- **Main remaining bridge:** admitted internal rationals/reals, graph arithmetic and finite coding; Archimedean small-gap lemma for additive inverses; multiplication/positive real division; supported code representatives and original-number transfer; atom-cover/represented joins; threshold converse and exact global/local state interpretation. No real field, main faithful-probability equivalence or C theorem is inferred from the external algebra.

The exact global/local premises, source notes, caveats and ownership are in [probability-bridge-audit.md](probability-bridge-audit.md). The global target is C + **boxed** Plenitude + **quantified** Infinity_e. The local target is C + Actuality + Atomicity_t + BC_t + quantified Infinity_e for current graph states only. No language extension was introduced.

## Priority repair for the integrator

Check `AtomicProbabilityFiniteConstructive` first. It proves witnessed removal, enumeration permutation and finite-subset cardinality directly from inductive constructors, without DecidableEq or classical library lemmas. If its reports pass, import it in the frozen scalar module and replace the bodies of:

- `Probability.enumeration_perm` with `ProbabilityFinite.enumeration_perm hx hy h`.
- `Probability.enumeration_subset_length` with `ProbabilityFinite.enumeration_subset_length hn hsub`.

Keep the original signatures if convenient; rerun `AtomicProbabilityAlgebraChecks` and inspect actual dependencies. The author has not edited the frozen files. Early recursive generalized-field notation failed in the initial scalar drafts; if needed, review the analogous recursion in `AtomicProbabilityComplete.joinList` and `JoinCompatible`.

## Serial commands

Run from the bundle root, by the designated integrator only. The pinned toolchain is `leanprover/lean4:v4.33.1`. The external algebra uses Init only. Shallow cuts depend on `Classicism.Core`; existing certificate infrastructure transitively imports `Mathlib.Data.Set.Finite.Basic`, whose availability remains the integrator’s responsibility. No full Mathlib build is requested.

```sh
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityFiniteConstructive --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityAlgebraChecks --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityComplete --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityNormalization --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityCutCertificates --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityCutArithmeticCertificates --timeout 180
python3 research/2026-10-22/lean-formalization/check_module.py Classicism.Results.Research.AtomicProbabilityCutNegationCertificates --timeout 180
```

If certification infrastructure is unavailable, shallow cut source modules may be checked first by omitting the `Certificates` suffix. This is not object-language certification. Import closure, claim levels and last observed verification: [probability-check-manifest.json](probability-check-manifest.json).

## Frozen source manifest

Hashes are at author handoff; repaired integrator versions are tracked by its own check manifests.

| Module | Handoff SHA-256 |
|---|---|
| [AtomicProbabilityScalar.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityScalar.lean) | `86a8c8a4377ab94e95384400a9b34515707e02b680de03cbf921f32d7bfa668e` |
| [AtomicProbabilityEnvelope.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityEnvelope.lean) | `ccff97610e11b0f8ceb9c9c865300a8e7f1af6632692ff48bbd14bd978da5739` |
| [ProbabilitySymmetryFinite.lean](../../../topics/classicism/lean/Classicism/Results/Research/ProbabilitySymmetryFinite.lean) | `97aed7ce1bb36666e27aefaad26faa079e39f958d7a8aee0f2dd97bb8de1673b` |
| [AtomicProbabilityFiniteFibres.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFiniteFibres.lean) | `97d3ad0d7f35520033bbdf6487b19dede67c71a4157d5fa3e6fe945b84d4e78d` |
| [AtomicProbabilityAlgebraChecks.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityAlgebraChecks.lean) | `ecc44696ab840b9e80d656c0e5abe8bc2cbb3597c57133567531ed8192e9a2a2` |
| [AtomicProbabilityCuts.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCuts.lean) | `4ff09558d1573e1a1c934ebb61c0bf92ce30bf9e4aaf11cf6e35d6a4539222dd` |
| [AtomicProbabilityCutAddition.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCutAddition.lean) | `af8bc192df7058fcc6d8079ae3f10501bcc09c433e26303bf97bb697e20a04fd` |
| [AtomicProbabilityCutCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCutCertificates.lean) | `dd2012bb88b6cce12157d1bddb945a741c753b9532f236689cbff068c67a6858` |
| [AtomicProbabilityCutArithmetic.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCutArithmetic.lean) | `1d1a2a78fbfbe1e9fe28c65f306a9b2758b8b784e7a8ffbe4eb2b20c783f970a` |
| [AtomicProbabilityCutArithmeticCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCutArithmeticCertificates.lean) | `eec6075570b4bc158927e4f242d752fa087e59247d74b9532f002e85995c3ae6` |
| [AtomicProbabilityComplete.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityComplete.lean) | `e819409bb98ce9d59cd4a0559d2a94c06860ba798c56bc43b0afbc6e9e229e82` |
| [AtomicProbabilityNormalization.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityNormalization.lean) | `218be72a478fe14507e8790f5d760211360de28c79fdd15c25038122f51e5a97` |
| [AtomicProbabilityCutNegation.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCutNegation.lean) | `6b474af72c4d83e0e51b2b206b49961a49ee98aff928b791cc72756703898b18` |
| [AtomicProbabilityCutNegationCertificates.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityCutNegationCertificates.lean) | `e5e28c8ceda8a3ffbf92a92aab46b203aeabd0721b0d92cedbe05de3e2668f5d` |
| [AtomicProbabilityFiniteConstructive.lean](../../../topics/classicism/lean/Classicism/Results/Research/AtomicProbabilityFiniteConstructive.lean) | `b497646b45fd47af7a70684864c90ee482112e85619abd876ccce6b2e3a5e40b` |

Original notes, record YAML, model assertions, generated `Statements.lean` and database Lean statuses were preserved. No author check changed any database verification flag.

## Authorized continuation: concrete internal work

Eight fresh sources/drivers are frozen and ready: see [probability-internal-status.md](probability-internal-status.md) for their exact mathematical scope, hashes and serial check targets. The original fifteen files remain with the integrator. The supported cut representatives/extensionality, internal least-number step and represented Cantor diagonal are now concrete source proofs rather than uninstantiated interfaces. Compilation and object-language certification remain pending.
