import Classicism.Models.CoalescedFirstOrder
import Classicism.Models.ChoiceFirstOrderAxiomTheory
import Classicism.Results.Research.CoalescedCHModel
import Mathlib.ModelTheory.Satisfiability

/-!
# From explicit first-order witness theories to CH countermodels

Original formalization, misc, Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. The source assumptions here are models, or satisfiability,
of the displayed ordinary first-order theories. The theory contains the
actual comprehension axioms and the actual translation of a pure sentence.

Recovery constructs the sorted structure and proves its comprehension;
`CoalescedFirstOrder` transfers it to the coalescence singleton category;
`CoalescedCHModel` proves the root failure from terminal truth. Neither C
modelhood nor the desired CH conclusion is a field in an assumed package.

The remaining set-theoretic obligation is to derive satisfiability of these
particular theories from the appropriate ZFC models. This file proves no
Con(ZFC) theorem, CH independence, or internal-real interpretation theorem.
-/

namespace Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer

open AxiomSet Intensional ChoiceFirstOrder.MathlibBridge

/-- Explicit first-order axioms plus the translated original pure sentence. -/
def witnessTheory (p : Sentence Signature.pure) : language.Theory :=
  AxiomTheory.theory ∪ {sentence p}

abbrev chTheory (σ : Ty) : language.Theory := witnessTheory (existsRealCH σ)
abbrev notCHTheory (σ : Ty) : language.Theory := witnessTheory (existsRealNotCH σ)

def baseModel (p : Sentence Signature.pure) (M : Type) [language.Structure M]
    (hM : FirstOrder.Language.Theory.Model M (witnessTheory p)) :
    FirstOrder.Language.Theory.Model M AxiomTheory.theory :=
  hM.mono Set.subset_union_left

theorem witness_realize (p : Sentence Signature.pure) (M : Type) [language.Structure M]
    (hM : FirstOrder.Language.Theory.Model M (witnessTheory p)) :
    FirstOrder.Language.Sentence.Realize M (sentence p) :=
  hM.realize_of_mem _ (Or.inr rfl)

/-- The component is constructed from the recovered sorted domains. -/
def component (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M AxiomTheory.theory) :
    Premodel Signature.pure Coalesced.One :=
  Coalesced.FirstOrderBridge.model (AxiomTheory.recoveredStructure M hT)

theorem component_isModel (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M AxiomTheory.theory) :
    (component M hT).IsModel :=
  Coalesced.FirstOrderBridge.isModel (AxiomTheory.recoveredStructure M hT)
    (AxiomTheory.recovered_smallComprehension M hT)

theorem component_sentence_correct (M : Type) [language.Structure M]
    (hT : FirstOrder.Language.Theory.Model M AxiomTheory.theory)
    (p : Sentence Signature.pure) :
    FirstOrder.Language.Sentence.Realize M (sentence p) ↔
      (component M hT).HoldsSentence p :=
  (AxiomTheory.recovered_sentence_correct M hT p).trans
    (Coalesced.FirstOrderBridge.holdsSentence_iff
      (AxiomTheory.recoveredStructure M hT) p).symm

theorem component_of_model (p : Sentence Signature.pure)
    (M : Type) [language.Structure M]
    (hM : FirstOrder.Language.Theory.Model M (witnessTheory p)) :
    ∃ A : Premodel Signature.pure Coalesced.One, A.IsModel ∧ A.HoldsSentence p := by
  let hT := baseModel p M hM
  exact ⟨component M hT, component_isModel M hT,
    (component_sentence_correct M hT p).mp (witness_realize p M hM)⟩

/-- This language is in universe zero, so Mathlib's satisfiability gives a
carrier of exactly the size required by the existing intensional semantics. -/
theorem component_of_satisfiable (p : Sentence Signature.pure)
    (hs : (witnessTheory p).IsSatisfiable) :
    ∃ A : Premodel Signature.pure Coalesced.One, A.IsModel ∧ A.HoldsSentence p := by
  obtain ⟨M⟩ := hs
  exact component_of_model p (M : Type) (inferInstance :
    FirstOrder.Language.Theory.Model M (witnessTheory p))

theorem consistent_of_model (p : Sentence Signature.pure)
    (M : Type) [language.Structure M]
    (hM : FirstOrder.Language.Theory.Model M (witnessTheory p)) :
    Consistent (single p) := by
  obtain ⟨A, hA, hp⟩ := component_of_model p M hM
  exact Consistent.of_model A hA (A.holdsAx_single hp)

theorem consistent_of_satisfiable (p : Sentence Signature.pure)
    (hs : (witnessTheory p).IsSatisfiable) : Consistent (single p) := by
  obtain ⟨A, hA, hp⟩ := component_of_satisfiable p hs
  exact Consistent.of_model A hA (A.holdsAx_single hp)

theorem countermodel_of_models (σ : Ty)
    (M N : Type) [language.Structure M] [language.Structure N]
    (hM : FirstOrder.Language.Theory.Model M (chTheory σ))
    (hN : FirstOrder.Language.Theory.Model N (notCHTheory σ)) :
    ∃ A : Premodel Signature.pure Coalesced.World,
      A.IsModel ∧ ¬ A.HoldsSentence (nonContingency σ) := by
  obtain ⟨L, hL, hCH⟩ := component_of_model (existsRealCH σ) M hM
  obtain ⟨R, hR, hNotCH⟩ := component_of_model (existsRealNotCH σ) N hN
  exact ⟨Coalesced.model L R, coalesced_countermodel L R hL hR σ hCH hNotCH⟩

theorem countermodel_of_satisfiable (σ : Ty)
    (hCH : (chTheory σ).IsSatisfiable)
    (hNotCH : (notCHTheory σ).IsSatisfiable) :
    ∃ A : Premodel Signature.pure Coalesced.World,
      A.IsModel ∧ ¬ A.HoldsSentence (nonContingency σ) := by
  obtain ⟨L, hL, hp⟩ := component_of_satisfiable (existsRealCH σ) hCH
  obtain ⟨R, hR, hq⟩ := component_of_satisfiable (existsRealNotCH σ) hNotCH
  exact ⟨Coalesced.model L R, coalesced_countermodel L R hL hR σ hp hq⟩

theorem maximalism_inconsistent_of_models (σ : Ty) (hσ : σ.Closed)
    (M N : Type) [language.Structure M] [language.Structure N]
    (hM : FirstOrder.Language.Theory.Model M (chTheory σ))
    (hN : FirstOrder.Language.Theory.Model N (notCHTheory σ)) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ single (nonContingency σ)) :=
  maximalism_inconsistent σ hσ
    (consistent_of_model (existsRealCH σ) M hM)
    (consistent_of_model (existsRealNotCH σ) N hN)

theorem maximalism_inconsistent_of_satisfiable (σ : Ty) (hσ : σ.Closed)
    (hCH : (chTheory σ).IsSatisfiable)
    (hNotCH : (notCHTheory σ).IsSatisfiable) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ single (nonContingency σ)) :=
  maximalism_inconsistent σ hσ
    (consistent_of_satisfiable (existsRealCH σ) hCH)
    (consistent_of_satisfiable (existsRealNotCH σ) hNotCH)

theorem maximalism_schema_inconsistent_of_satisfiable (σ : Ty) (hσ : σ.Closed)
    (hCH : (chTheory σ).IsSatisfiable)
    (hNotCH : (notCHTheory σ).IsSatisfiable) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪
      Classicism.Research.CoalescedCH.NonContingency.schema) :=
  maximalism_schema_inconsistent σ hσ
    (consistent_of_satisfiable (existsRealCH σ) hCH)
    (consistent_of_satisfiable (existsRealNotCH σ) hNotCH)

#print axioms component_of_model
#print axioms component_of_satisfiable
#print axioms countermodel_of_satisfiable
#print axioms maximalism_inconsistent_of_satisfiable
#print axioms maximalism_schema_inconsistent_of_satisfiable

end Classicism.Meta.Research.CoalescedCH.FirstOrderTransfer
