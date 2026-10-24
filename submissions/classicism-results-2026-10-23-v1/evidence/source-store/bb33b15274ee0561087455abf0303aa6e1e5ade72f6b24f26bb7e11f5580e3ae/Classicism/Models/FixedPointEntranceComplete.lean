import Classicism.Models.FixedPointEntranceSeparation
import Classicism.Models.FixedPointEntranceLeibniz

/-!
# The full qualitative-link fixed-point entrance package

Original assembly (misc), 23 October 2026. Direct source:
`research/2026-10-22/notes/fixed-point-entrance-cone.md`, sections 1--6
(unpaginated). This statement includes every positive root schema and
every failure in the source statement. Its Lean status is controlled by
the matching complete check and axiom audit, not by this source file.
-/

namespace Classicism.Meta.Intensional.FixedPointEntrance.Qualitative

theorem full_countermodel :
    model.IsModel ∧
    (∀ W : cone.Ob, Subsingleton (model.Dom W .e)) ∧
    model.HoldsAx Background ∧
    ¬ model.HoldsSentence (Term.box (P.TameRigidity.quoted TameWitness.ut)) ∧
    (∀ ρ : RTy, ¬ model.HoldsSentence (P.Barcan.quoted (.rel ρ))) ∧
    ¬ model.HoldsSentence (Sentence.nd (.rel .t)) ∧
    (∀ ρ : RTy, ¬ model.HoldsSentence (P.StrongLeibniz.quoted ρ)) ∧
    ¬ model.HoldsSentence P.StrongLeibnizT.quoted :=
  ⟨isModel, individual_singleton, holds_background, root_not_box_tame,
    RelationalBarcan.not_barcan_relational, Distinctness.not_nd_t,
    Leibniz.not_strongLeibniz, Leibniz.not_strongLeibniz_t⟩

end Classicism.Meta.Intensional.FixedPointEntrance.Qualitative
