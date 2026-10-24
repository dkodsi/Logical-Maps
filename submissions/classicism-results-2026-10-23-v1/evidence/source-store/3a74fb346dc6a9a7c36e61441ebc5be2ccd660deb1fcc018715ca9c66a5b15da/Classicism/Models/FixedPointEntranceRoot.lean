import Classicism.Models.FixedPointEntrance
import Classicism.Models.FixedPointEntranceChoice
import Classicism.Models.FixedPointEntranceBarcan
import Classicism.Models.FixedPointEntrancePowers

/-!
# The actual root package of the qualitative-link entrance

Original assembly (misc), 23 October 2026, of the root verdicts in
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, sections 1--4 and 6
(unpaginated). These root properties do not certify the higher-type tail
counterexample to Tame Rigidity or failure of boxed Tame Rigidity.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative

theorem root_package :
    model.IsModel ∧
    (∀ W : cone.Ob, Subsingleton (model.Dom W .e)) ∧
    model.HoldsAx P.Atomicity.schema ∧
    model.HoldsAx P.BooleanCompleteness.schema ∧
    model.HoldsAx P.RigidComprehension.schema ∧
    model.HoldsAx P.RelationalChoice.schema ∧
    model.HoldsAx P.TameRigidity.schema ∧
    model.HoldsAx P.RigidPower.schema ∧
    model.HoldsAx P.WeaklyRigidPower.schema ∧
    model.HoldsSentence (Sentence.bf .e) ∧
    ¬ model.HoldsSentence (P.Barcan.quoted (.rel .t)) ∧
    ¬ model.HoldsSentence (Sentence.nd (.rel .t)) :=
  ⟨isModel, individual_singleton, Atomicity.holds_atomicity_schema,
    Completeness.holds_bc_schema, Comprehension.holds_rigid_comprehension_schema,
    RelationalChoice.holds_relational_choice_schema, Rigidity.holds_tame_schema,
    Powers.holds_rigid_power_schema, Powers.holds_weak_power_schema,
    Distinctness.bf_e, Barcan.not_barcan_t, Distinctness.not_nd_t⟩

end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative
