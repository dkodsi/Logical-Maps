import Classicism.Results.Research.SectionsRetractionsChoice
import Classicism.Results.Research.SectionsRetractionsPlenitude

/-! Forward directions for the full schema assemblies. Direct sources are
Classicism §2.3, Propositions 2.13–2.15, and the existing research notes cited
by the imported reverse-direction modules. -/
namespace Classicism.Research.Splitting
open Classicism.P

theorem functional_choice_actuality : FunctionalChoice Prop Prop → Actuality :=
  fun fc => Proofs.plenitude_r_implies_actuality
    (Proofs.functional_choice_r_implies_plenitude_r fc)

theorem plenitude_actuality : Plenitude Prop Prop → Actuality :=
  Proofs.plenitude_r_implies_actuality

end Classicism.Research.Splitting
