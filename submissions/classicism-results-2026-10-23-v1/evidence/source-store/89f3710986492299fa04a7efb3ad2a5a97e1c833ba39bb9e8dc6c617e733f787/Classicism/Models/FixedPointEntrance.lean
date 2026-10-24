import Classicism.Models.FixedPointEntranceRigidity
import Classicism.Models.FixedPointEntranceCompleteness
import Classicism.Models.FixedPointEntranceComprehension
import Classicism.Models.FixedPointEntranceDistinctness

/-!
# Checked scope of the qualitative-link fixed-point entrance

Original supporting formalization (misc), 23 October 2026. Source:
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, sections 1--3 and 6
(unpaginated). This assembly states exactly its proved root properties.
It does not yet assert the full rigidity.32 separator: the higher-type tail
witness and the root power/atomicity/choice verdicts require further proofs.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative

/-- The actual constructed model and the root verdicts proved in this
package. No semantic verdict occurs among the hypotheses. -/
theorem root_profile :
    model.IsModel ∧
    (∀ W : cone.Ob, Subsingleton (model.Dom W .e)) ∧
    model.HoldsAx P.BooleanCompleteness.schema ∧
    model.HoldsAx P.RigidComprehension.schema ∧
    model.HoldsAx P.TameRigidity.schema ∧
    model.HoldsSentence (Sentence.bf .e) ∧
    ¬ model.HoldsSentence (Sentence.nd (.rel .t)) :=
  ⟨isModel, individual_singleton, Completeness.holds_bc_schema,
    Comprehension.holds_rigid_comprehension_schema, Rigidity.holds_tame_schema,
    Distinctness.bf_e, Distinctness.not_nd_t⟩

end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative
