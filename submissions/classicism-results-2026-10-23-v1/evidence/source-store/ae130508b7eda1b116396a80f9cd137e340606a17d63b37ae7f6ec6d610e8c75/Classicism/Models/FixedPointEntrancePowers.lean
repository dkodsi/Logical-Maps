import Classicism.Models.FixedPointEntranceAtomicity
import Classicism.Models.FixedPointEntranceComprehension
import Classicism.Results.Research.RigidityClosureResearchContinuationSchemas

/-!
# Root rigid powers from actual atomicity and comprehension

Original supporting assembly (misc), 23 October 2026. Source:
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, section 4
(unpaginated). This formal route applies the independently certified
full-schema Atomicity + RC => WRP theorem to the actual root verdicts.
The ordinary note also contains a direct exact-image proof. Neither route
asserts the corresponding boxed principles at the tail.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Powers

theorem holds_weak_power_schema : model.HoldsAx P.WeaklyRigidPower.schema :=
  model.entails_holds isModel
    Classicism.Meta.Research.RigidityClosure.atomicity_rc_weak_power
    (model.holdsAx_union Atomicity.holds_atomicity_schema
      Comprehension.holds_rigid_comprehension_schema)

theorem holds_rigid_power_schema : model.HoldsAx P.RigidPower.schema :=
  model.entails_holds isModel Classicism.Proofs.weakly_rigid_power_implies_rigid_power.entails
    (model.holdsAx_union holds_weak_power_schema holds_weak_power_schema)

end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative.Powers
