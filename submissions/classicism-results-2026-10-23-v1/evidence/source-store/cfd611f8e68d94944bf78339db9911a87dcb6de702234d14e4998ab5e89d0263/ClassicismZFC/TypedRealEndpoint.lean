import ClassicismZFC.TypedReal
import ClassicismZFC.TypedRealQuotation

/-!
# The constructed real tuple in the original quoted object language

The real-existence endpoint has only ordinary ZFC satisfaction and the literal
source complete-field formula as assumptions. The two CH assembly lemmas
add the explicitly displayed verdict for this constructed tuple; the separate
internal cardinality proof must supply that verdict. They do not identify
ordinal CH with structural CH by assumption.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Erdos501.FOL (L memM)
open Classicism.Meta

namespace ClassicismZFC.TypedReal

variable {M : Type} [L.Structure M]
variable (hZFC : M ⊨ Erdos501.FOL.ZFC)
variable {E Add Mul Lt zero one : M}
variable (H : SourceFieldSemantics.Field E Add Mul Lt zero one)

/-- The actually constructed seven objects satisfy the original HasReal term
in the actual singleton component used by coalescence. -/
theorem component_hasReal :
    (InternalHierarchy.component hZFC E ⟨zero, H.zero_mem⟩).HoldsSentence
      (Classicism.Research.Analytic.HasReal.term .e) := by
  apply (Intensional.Coalesced.FirstOrderBridge.holdsSentence_iff
    (hierarchy hZFC H) _).mpr
  apply (TypedRealQuotation.holds_hasReal_iff (hierarchy hZFC H)
    (InternalHierarchy.firstOrder_isModel hZFC E ⟨zero, H.zero_mem⟩)).mpr
  exact ⟨domain hZFC H, order hZFC H, addition hZFC H, multiplication hZFC H,
    zeroValue hZFC H, oneValue hZFC H, naturals hZFC H, isReal hZFC H⟩

/-- The source field hypothesis is actual first-order formula satisfaction. -/
theorem component_hasReal_of_isField
    (h : RealFieldSentence.IsField E Add Mul Lt zero one) :
    (InternalHierarchy.component hZFC E
      ⟨zero, (SourceFieldSemantics.of_isField h).zero_mem⟩).HoldsSentence
      (Classicism.Research.Analytic.HasReal.term .e) :=
  component_hasReal hZFC (SourceFieldSemantics.of_isField h)

/-- Assemble a structural-CH proof at the chosen real tuple into the original
quoted positive existential. The cardinal comparison premise is explicit. -/
theorem component_hasRealCH
    (hCH : TypedRealQuotation.StructuralCH (hierarchy hZFC H)
      (domain hZFC H) (naturals hZFC H)) :
    (InternalHierarchy.component hZFC E ⟨zero, H.zero_mem⟩).HoldsSentence
      (Classicism.Meta.Research.CoalescedCH.existsRealCH .e) := by
  apply (Intensional.Coalesced.FirstOrderBridge.holdsSentence_iff
    (hierarchy hZFC H) _).mpr
  apply (TypedRealQuotation.holds_existsRealCH_iff (hierarchy hZFC H)
    (InternalHierarchy.firstOrder_isModel hZFC E ⟨zero, H.zero_mem⟩)).mpr
  exact ⟨domain hZFC H, order hZFC H, addition hZFC H, multiplication hZFC H,
    zeroValue hZFC H, oneValue hZFC H, naturals hZFC H, isReal hZFC H, hCH⟩

/-- The same assembly for a negative structural-CH witness. -/
theorem component_hasRealNotCH
    (hCH : ¬ TypedRealQuotation.StructuralCH (hierarchy hZFC H)
      (domain hZFC H) (naturals hZFC H)) :
    (InternalHierarchy.component hZFC E ⟨zero, H.zero_mem⟩).HoldsSentence
      (Classicism.Meta.Research.CoalescedCH.existsRealNotCH .e) := by
  apply (Intensional.Coalesced.FirstOrderBridge.holdsSentence_iff
    (hierarchy hZFC H) _).mpr
  apply (TypedRealQuotation.holds_existsRealNotCH_iff (hierarchy hZFC H)
    (InternalHierarchy.firstOrder_isModel hZFC E ⟨zero, H.zero_mem⟩)).mpr
  exact ⟨domain hZFC H, order hZFC H, addition hZFC H, multiplication hZFC H,
    zeroValue hZFC H, oneValue hZFC H, naturals hZFC H, isReal hZFC H, hCH⟩

include hZFC in
/-- Existence of a source field produces an actual one-world C model with
the original object-language real-existence sentence. -/
theorem exists_component_hasReal (hfield : M ⊨ RealFieldSentence.ExistsRealField) :
    ∃ A : Intensional.Premodel Signature.pure Intensional.Coalesced.One,
      A.IsModel ∧ A.HoldsSentence (Classicism.Research.Analytic.HasReal.term .e) := by
  obtain ⟨E, Add, Mul, Lt, zero, one, hf⟩ :=
    RealFieldSentence.realize_ExistsRealField.mp hfield
  let H' := SourceFieldSemantics.of_isField hf
  exact ⟨InternalHierarchy.component hZFC E ⟨zero, H'.zero_mem⟩,
    InternalHierarchy.component_isModel hZFC E ⟨zero, H'.zero_mem⟩,
    component_hasReal hZFC H'⟩

#print axioms component_hasReal
#print axioms component_hasReal_of_isField
#print axioms component_hasRealCH
#print axioms component_hasRealNotCH
#print axioms exists_component_hasReal

end ClassicismZFC.TypedReal
