import ClassicismZFC.CodedFieldForcing
import ClassicismZFC.CHOrdinalDirection
import ClassicismZFC.TypedCHTransport
import ClassicismZFC.SelectedFieldForcing
import Classicism.Results.Research.CoalescedCHModel

/-!
# Actual components for the opposite-CH construction

Original source, misc, 23 October 2026. All displayed component existence
claims construct the model from the selected ordinary membership model and
the proved finite formula witnesses. No assumed component, real field,
standard natural-number identification, or structural-CH equivalence occurs
in their premises. This is an ambient-Lean-metatheoretic construction; the
qualification in OppositeCH about finitistic relative consistency remains.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Classicism.Meta Classicism.Meta.Intensional
open Classicism.Meta.Intensional.Coalesced (One)

namespace ClassicismZFC.OppositeCHComponents

open CHCardinality CHFieldTransport

/-- The selected collapse witness gives an actual one-world C model of the
original quoted positive real-field CH sentence. -/
theorem positive_component :
    ∃ A : Premodel Signature.pure One,
      A.IsModel ∧ (∀ σ, Nonempty (A.Dom .point σ)) ∧
      A.HoldsSentence (Research.CoalescedCH.existsRealCH .e) := by
  obtain ⟨R, Plus, Times, Lt, zero, one, N, hF, hN, hCH⟩ :=
    SelectedFieldForcing.positive_real_witnesses
  have hZFC := SelectedFieldForcing.modelsZFC
  let H := SourceFieldSemantics.of_isField hF
  refine ⟨InternalHierarchy.component hZFC R ⟨zero, H.zero_mem⟩,
    InternalHierarchy.component_isModel hZFC R ⟨zero, H.zero_mem⟩, ?_, ?_⟩
  · intro σ
    exact InternalHierarchy.component_nonempty hZFC R ⟨zero, H.zero_mem⟩ .point σ
  · exact TypedCHTransport.component_hasRealCH hZFC H hN hCH

/-- The random-algebra witness gives an actual one-world C model satisfying
the original quoted existence of a real structure in which CH fails. -/
theorem negative_component :
    ∃ A : Premodel Signature.pure One,
      A.IsModel ∧ (∀ σ, Nonempty (A.Dom .point σ)) ∧
      A.HoldsSentence (Research.CoalescedCH.existsRealNotCH .e) := by
  obtain ⟨R, Plus, Times, Lt, zero, one, N, G, hF, hN, hG, hRP, hPR⟩ :=
    CodedFieldForcing.negative_cardinal_witnesses
  have hZFC := CodedFieldForcing.negative_modelsZFC
  have hRN := CHOrdinalDirection.not_structural_of_not_CH hZFC
    (schroeder_bernstein hZFC hRP hPR)
    (equinumerous_symm hZFC ⟨G, hG⟩)
    CodedFieldForcing.negative_package_and_not_CH.2
  let H := SourceFieldSemantics.of_isField hF
  refine ⟨InternalHierarchy.component hZFC R ⟨zero, H.zero_mem⟩,
    InternalHierarchy.component_isModel hZFC R ⟨zero, H.zero_mem⟩, ?_, ?_⟩
  · intro σ
    exact InternalHierarchy.component_nonempty hZFC R ⟨zero, H.zero_mem⟩ .point σ
  · exact TypedCHTransport.component_hasRealNotCH hZFC H hN hRN

/-- Both original object-language witnesses now have actual component models. -/
theorem opposite_components :
    ∃ L R : Premodel Signature.pure One,
      (L.IsModel ∧ (∀ σ, Nonempty (L.Dom .point σ)) ∧
        L.HoldsSentence (Research.CoalescedCH.existsRealCH .e)) ∧
      (R.IsModel ∧ (∀ σ, Nonempty (R.Dom .point σ)) ∧
        R.HoldsSentence (Research.CoalescedCH.existsRealNotCH .e)) := by
  obtain ⟨L, hL⟩ := positive_component
  obtain ⟨R, hR⟩ := negative_component
  exact ⟨L, R, hL, hR⟩

/-- The concrete coalesced C model has boxed Barcan at every type but fails
the original structural CH non-contingency sentence at type e. -/
theorem coalesced_countermodel :
    ∃ A : Premodel Signature.pure Coalesced.World,
      A.IsModel ∧ (∀ σ : Ty, A.HoldsSentence (Term.box (Sentence.bf σ))) ∧
      ¬ A.HoldsSentence (Research.CoalescedCH.nonContingency .e) := by
  obtain ⟨L, R, ⟨hL, hnL, hcL⟩, ⟨hR, hnR, hcR⟩⟩ := opposite_components
  exact ⟨Coalesced.model L R,
    Research.CoalescedCH.coalesced_box_barcan_countermodel
      L R hL hR hnL hnR .e hcL hcR⟩

/-- These are consistency witnesses in the existing Classicism proof system,
obtained by model soundness, not new consistency axioms. -/
theorem consistent_opposite_witnesses :
    AxiomSet.Consistent (AxiomSet.single (Research.CoalescedCH.existsRealCH .e)) ∧
    AxiomSet.Consistent (AxiomSet.single (Research.CoalescedCH.existsRealNotCH .e)) := by
  obtain ⟨L, R, ⟨hL, _, hcL⟩, ⟨hR, _, hcR⟩⟩ := opposite_components
  exact Research.CoalescedCH.consistent_witnesses_of_components
    L R hL hR .e hcL hcR

/-- This refutes Maximalism TOGETHER WITH CH non-contingency, not Maximalism
alone. The distinction is part of the theorem's actual statement. -/
theorem maximalism_with_CH_noncontingency_inconsistent :
    ¬ AxiomSet.Consistent
      (AxiomSet.maximalist (Sig := Signature.pure) ∪
        AxiomSet.single (Research.CoalescedCH.nonContingency .e)) := by
  obtain ⟨L, R, ⟨hL, _, hcL⟩, ⟨hR, _, hcR⟩⟩ := opposite_components
  exact Research.CoalescedCH.maximalism_inconsistent_of_components
    L R hL hR .e Ty.closed_e hcL hcR

theorem maximalism_with_CH_noncontingency_schema_inconsistent :
    ¬ AxiomSet.Consistent
      (AxiomSet.maximalist (Sig := Signature.pure) ∪
        Classicism.Research.CoalescedCH.NonContingency.schema) := by
  obtain ⟨L, R, ⟨hL, _, hcL⟩, ⟨hR, _, hcR⟩⟩ := opposite_components
  exact Research.CoalescedCH.maximalism_schema_inconsistent_of_components
    L R hL hR .e Ty.closed_e hcL hcR

#print axioms positive_component
#print axioms negative_component
#print axioms opposite_components
#print axioms coalesced_countermodel
#print axioms consistent_opposite_witnesses
#print axioms maximalism_with_CH_noncontingency_inconsistent
#print axioms maximalism_with_CH_noncontingency_schema_inconsistent

end ClassicismZFC.OppositeCHComponents
