import Classicism.Models.CoalescedModel
import Classicism.Results.Research.CoalescedCHMaximalism

/-!
# Opposite-CH components give a coalesced countermodel

Original research, misc, Codex (OpenAI), prompted by Daniel Kodsi,
23 October 2026. The concrete coalesced premodel and its term-closure proof are
those of `Models.CoalescedModel`. This module supplies its CH application.

The hypotheses provide two actual one-world models with opposite structural CH
witnesses. Their existence is not proved or postulated here. In particular,
there is no Con(ZFC) axiom and no use of externally full powersets in place of
the components' internal Henkin relation domains.
-/

namespace Classicism.Meta.Research.CoalescedCH

open AxiomSet CategoryTheory Intensional Intensional.Coalesced

/-- A singleton component's distinguished object is its sole point. Stating
the transport this way avoids any definitional assumption about `A.W₀`. -/
theorem holds_point_iff_sentence (A : Premodel Signature.pure One)
    (p : Sentence Signature.pure) :
    A.Holds (W := One.point) (PUnit.unit : A.W₀ ⟶ One.point) p .nil ↔ A.HoldsSentence p := by
  have h : ∀ W : One,
      A.Holds (W := W) (PUnit.unit : A.W₀ ⟶ W) p .nil ↔
        A.Holds (W := One.point) (PUnit.unit : A.W₀ ⟶ One.point) p .nil := by
    intro W
    cases W
    rfl
  exact (h A.W₀).symm

variable (L R : Premodel Signature.pure One)

theorem consistent_witnesses_of_components
    (hL : L.IsModel) (hR : R.IsModel) (σ : Ty)
    (hCH : L.HoldsSentence (existsRealCH σ))
    (hNotCH : R.HoldsSentence (existsRealNotCH σ)) :
    Consistent (single (existsRealCH σ)) ∧
      Consistent (single (existsRealNotCH σ)) :=
  ⟨Consistent.of_model L hL (L.holdsAx_single hCH),
    Consistent.of_model R hR (R.holdsAx_single hNotCH)⟩

/-- The root failure is proved from terminal evaluation transfer, not assumed. -/
theorem coalesced_not_nonContingency
    (hL : L.IsModel) (hR : R.IsModel) (σ : Ty)
    (hCH : L.HoldsSentence (existsRealCH σ))
    (hNotCH : R.HoldsSentence (existsRealNotCH σ)) :
    ¬ (model L R).HoldsSentence (nonContingency σ) := by
  apply not_holds_nonContingency_of_accessible (model L R)
    (isModel L R hL hR) σ toRight toLeft
  · exact (holds_right L R (existsRealNotCH σ) .nil).2
      ((holds_point_iff_sentence R _).2 hNotCH)
  · exact (holds_left L R (existsRealCH σ) .nil).2
      ((holds_point_iff_sentence L _).2 hCH)

theorem coalesced_countermodel
    (hL : L.IsModel) (hR : R.IsModel) (σ : Ty)
    (hCH : L.HoldsSentence (existsRealCH σ))
    (hNotCH : R.HoldsSentence (existsRealNotCH σ)) :
    (model L R).IsModel ∧ ¬ (model L R).HoldsSentence (nonContingency σ) :=
  ⟨isModel L R hL hR, coalesced_not_nonContingency L R hL hR σ hCH hNotCH⟩

theorem maximalism_inconsistent_of_components
    (hL : L.IsModel) (hR : R.IsModel) (σ : Ty) (hσ : σ.Closed)
    (hCH : L.HoldsSentence (existsRealCH σ))
    (hNotCH : R.HoldsSentence (existsRealNotCH σ)) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ single (nonContingency σ)) := by
  have h := consistent_witnesses_of_components L R hL hR σ hCH hNotCH
  exact maximalism_inconsistent σ hσ h.1 h.2

theorem maximalism_schema_inconsistent_of_components
    (hL : L.IsModel) (hR : R.IsModel) (σ : Ty) (hσ : σ.Closed)
    (hCH : L.HoldsSentence (existsRealCH σ))
    (hNotCH : R.HoldsSentence (existsRealNotCH σ)) :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪
      Classicism.Research.CoalescedCH.NonContingency.schema) := by
  have h := consistent_witnesses_of_components L R hL hR σ hCH hNotCH
  exact maximalism_schema_inconsistent σ hσ h.1 h.2

/-- With inhabited component domains the same concrete model has boxed Barcan
at every type, while structural CH non-contingency fails at the indicated type. -/
theorem coalesced_box_barcan_countermodel
    (hL : L.IsModel) (hR : R.IsModel)
    (hneL : ∀ τ, Nonempty (L.Dom .point τ))
    (hneR : ∀ τ, Nonempty (R.Dom .point τ))
    (σ : Ty)
    (hCH : L.HoldsSentence (existsRealCH σ))
    (hNotCH : R.HoldsSentence (existsRealNotCH σ)) :
    (model L R).IsModel ∧
      (∀ τ : Ty, (model L R).HoldsSentence (Term.box (Sentence.bf τ))) ∧
      ¬ (model L R).HoldsSentence (nonContingency σ) :=
  ⟨isModel L R hL hR,
    fun τ => holds_box_bf L R hL hR hneL hneR τ (𝟙 (model L R).W₀),
    coalesced_not_nonContingency L R hL hR σ hCH hNotCH⟩

#print axioms consistent_witnesses_of_components
#print axioms coalesced_countermodel
#print axioms maximalism_inconsistent_of_components
#print axioms maximalism_schema_inconsistent_of_components
#print axioms coalesced_box_barcan_countermodel

end Classicism.Meta.Research.CoalescedCH
