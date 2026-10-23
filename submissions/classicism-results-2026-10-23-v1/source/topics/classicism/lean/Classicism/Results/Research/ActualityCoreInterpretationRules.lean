import Classicism.Results.Research.ActualityCore
import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Tools.Translate

/-!
# Object-language rules for the recursive local interpretation

Direct source: `research/2026-10-22/notes/actuality-world-slice-core.md`,
sections 2--3 (misc, 22 October 2026, unpaginated).

The existing cut and section proofs are put in a quantifier order suitable for
instantiation by the deep syntax induction. The generated declarations are
actual C derivations, not extra semantic closure assumptions.
-/

namespace Classicism.Research.ActualityCore
open Classicism.Paper Classicism.P

theorem interpretation_cut_rule {τ : Type} [Rel τ] [Order τ] [Pointwise τ]
    (w : Prop) (A X : τ) : ActualWorld w → Domain w A (Cut A X) :=
  fun hw => cut_in_domain w hw A X

theorem interpretation_section_rule {τ σ : Type}
    [Rel τ] [Order τ] [Pointwise τ] [Ty σ]
    (w : Prop) (D : σ → Prop) (A : τ) (F : σ → τ) (a : σ) :
    Domain w (ProductSupport D A) F → Domain w A (F a) :=
  fun hF => section_in_domain w D A F hF a

end Classicism.Research.ActualityCore

#classicism_check Classicism.Research.ActualityCore.interpretation_cut_rule
#classicism_check Classicism.Research.ActualityCore.interpretation_section_rule
#classicism_types Classicism.Research.ActualityCore.interpretation_cut_rule
#classicism_types Classicism.Research.ActualityCore.interpretation_section_rule
#classicism_derive Classicism.Research.ActualityCore.interpretation_cut_rule
#classicism_derive Classicism.Research.ActualityCore.interpretation_section_rule
#print axioms Classicism.Research.ActualityCore.interpretation_cut_rule.derivable
#print axioms Classicism.Research.ActualityCore.interpretation_section_rule.derivable
